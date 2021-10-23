import basic

open tactic expr

namespace hp

/-- A wrapper for metavariables. So I don't
have to error handle and type infer all the time. -/
@[derive decidable_eq]
meta structure stub :=
(mv : expr)
(type : expr)

namespace stub

meta def uniq_name : stub → name
| e := mvar_uniq_name e.mv

meta def pretty_name : stub → name
| e := mvar_pretty_name e.mv

meta def of_expr : expr → tactic stub
| e@(expr.mvar u p _) := stub.mk e <$> tactic.infer_type e
| _ := none

meta def to_expr : stub → expr
| s := s.mv

meta def to_type : stub → tactic expr
| s := infer_type $ to_expr s

meta def to_binder : stub → binder
| ⟨expr.mvar _ pn _, y⟩ := ⟨pn, binder_info.default, y⟩
| _ := undefined_core "to_binder failed for stub"

meta def mmap_exprs {T : Type → Type} [monad T] (f : telescope → expr → T expr) : telescope → stub → T stub
| Γ ⟨expr.mvar un pn x,y⟩ := pure stub.mk <*> (pure (expr.mvar un pn) <*> f Γ x) <*> f Γ y
| Γ ⟨x,y⟩ := pure stub.mk <*> f Γ x <*> f Γ y

meta def is_assigned : stub → tactic bool
| ⟨e@(expr.mvar _ _ _), _⟩ := tactic.is_assigned $ e
| s := pure tt

meta instance : assignable stub := ⟨@stub.mmap_exprs⟩
meta instance : has_coe stub expr := ⟨stub.to_expr⟩
meta instance : has_to_tactic_format stub := ⟨λ s, pure $ to_fmt $ pretty_name s⟩

/-- Return all of the mvars that the given mvar `x` depends on.
That is, return all of the mvars mentioned in the type of `x`.
If `x` is assigned, then also return the mvars that are present in the assignment.
 -/
meta def get_dependencies : stub → unsafe.type_context (list expr)
| ⟨e@(expr.mvar un _ _), et⟩ := do
  e ← unsafe.type_context.instantiate_mvars e,
  et ← unsafe.type_context.instantiate_mvars et,
  ems ← pure $ expr.list_mvars e,
  etms ← pure $ expr.list_mvars et,
  ms ← pure $ ems ++ etms,
  ms ← pure $ ms.filter (λ m, m.mvar_uniq_name ≠ un),
  pure ms
| _ := failure

/-- `depends_on x y` Returns true when `y` appears in the dependency list of `x`. -/
meta def depends_on : stub → stub → unsafe.type_context bool
| s₁ s₂ := do
  ds ← s₁.get_dependencies,
  pure $ list.any ds (λ d, mvar_uniq_name d = s₂.uniq_name)

variables {α : Type} [assignable α]
-- meta instance : has_mem stub α := ⟨λ h a, assignable.depends_on a h.to_expr⟩
-- meta instance (a : α) (h : stub) : decidable (h ∈ a) := infer_instance

meta def appears_in : stub → α → bool | s a := assignable.depends_on a s.to_expr

end stub

end hp