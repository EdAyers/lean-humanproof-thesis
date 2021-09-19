import basic

namespace hp

open tactic

/-- A helper type for local_constant. [todo] rename from hyp -/
@[derive decidable_eq]
meta structure hyp :=
(uniq_name : name)
(pretty_name : name)
(binder_info : binder_info)
(type : expr)

namespace hyp

meta def of_expr : expr → tactic hyp
| e@(expr.local_const u p bi type) := hyp.mk u p bi <$> tactic.infer_type e
| _ := none

meta def of_expr_tc : expr → tactic.unsafe.type_context hyp
| e@(expr.local_const u p bi type) := hyp.mk u p bi <$> tactic.unsafe.type_context.infer e
| _ := failure

meta def of_local_decl : local_decl → hyp
| d := hyp.mk d.unique_name d.pp_name d.bi d.type

meta def of_uniq_name : _root_.local_context → name → option hyp
| Γ n := of_local_decl <$> local_context.get_local_decl n Γ

meta def of_expr_lc : _root_.local_context → expr → option hyp
| Γ (expr.local_const un _ _ _) := of_uniq_name Γ un
| _ _ := none

meta def of_lc : _root_.local_context → list hyp
| Γ := list.reverse $ local_context.fold_decl (λ acc d, (of_local_decl d) :: acc) [] Γ

meta def to_expr : hyp → expr
| ⟨u,p,bi,y⟩ := expr.local_const u p bi y

meta def mmap_exprs {T : Type → Type} [monad T] (f : telescope → expr → T expr) : telescope → hyp → T hyp
| Γ ⟨u,p,bi,y⟩ := pure (hyp.mk u p bi) <*> f Γ y

meta def is_prop : hyp → tactic bool :=
tactic.is_prop ∘ hyp.type

meta instance : assignable hyp := ⟨@hyp.mmap_exprs⟩
meta instance : has_coe hyp expr := ⟨hyp.to_expr⟩
meta instance : has_to_tactic_format hyp := ⟨pp ∘ to_expr⟩

meta def to_binder : hyp → binder
| ⟨_, pn, bi, y⟩ := ⟨pn, bi, y⟩

meta def to_pi : hyp → expr → expr
| ⟨un, pn, bi, y⟩ b := expr.pi pn bi y $ expr.abstract_local b un

meta def to_pis : list hyp → expr → expr
| hs e := list.foldr to_pi e hs

variables {α : Type} [assignable α]
-- meta instance : has_mem hyp α := ⟨λ h a, assignable.depends_on a h.to_expr⟩
-- meta instance (a : α) (h : hyp) : decidable (h ∈ a) := infer_instance

meta def appears_in : hyp → α → bool | h a := assignable.depends_on a h.to_expr

end hyp

end hp