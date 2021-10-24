import .binder .expr

/-- A list of binders where the first binder is the _innermost_ one. Note that this is a different convention to
the list of binders created by `expr.pi_binders`. -/
meta def telescope := list binder

/-- A list of binders where the first binder is the _outermost_ one. -/
meta def cotelescope := list binder

namespace telescope

meta instance : has_append telescope := list.has_append
-- meta instance : has_to_tactic_format telescope := ⟨tactic.pp ∘ list.reverse⟩

meta def to_pis : expr → telescope → expr
| b (h :: t) := to_pis (binder.to_pi h b) t
| b [] := b

meta def to_lams : expr → telescope → expr
| b (h :: t) := to_lams (binder.to_lam h b) t
| b [] := b

meta def binders_aux (once : expr → option (binder × expr)) : list binder → expr → (list binder × expr)
| acc x := (acc, x) <| ((once x) >>= (λ ⟨h,b⟩, binders_aux (h::acc) b))

meta def n_binders_aux (once : expr → option (binder × expr)) : nat → list binder → expr → option (list binder × expr)
| 0 acc x := some (acc, x)
| (n+1) acc x := ((once x) >>= (λ ⟨h,b⟩, n_binders_aux n (h::acc) b))

meta def mbinders_aux {m} [monad m] [alternative m] (once : expr → m (binder × expr)) : list binder → expr → m (list binder × expr)
| acc x := ((once x) >>= (λ ⟨h,b⟩, mbinders_aux (h::acc) b)) <|> pure (acc, x)

/- Like binder.pi_binders except that the ordering of binders is reversed. -/
meta def of_pis : expr → (telescope × expr) := binders_aux expr.pi_binder []

meta def of_lams : expr → (telescope × expr) := binders_aux expr.lam_binder []

meta def of_exists : expr → (telescope × expr) := binders_aux expr.exists_binder []

meta def of_exists_conj : expr → tactic (telescope × expr) := mbinders_aux expr.exists_conj_binder []

meta def of_n_pis : expr → nat → option (telescope × expr)
| e n := n_binders_aux expr.pi_binder n [] e

meta def of_n_lams : expr → nat → option (telescope × expr)
| e n := n_binders_aux expr.lam_binder n [] e

private meta def to_locals_folder : binder → list expr → tactic (list expr)
| ⟨n, bi, y⟩ acc := do h ← tactic.mk_local' n bi (expr.instantiate_vars y acc), pure $ h :: acc

meta def to_locals : list binder → tactic (list expr)
| ctxt := list.mfoldr to_locals_folder [] ctxt

open tactic.unsafe

meta def push_type_context_core : binder → list expr → type_context (list expr)
| ⟨n, bi, y⟩ acc := do h ← type_context.push_local n (expr.instantiate_vars y acc) bi, pure $ h :: acc

meta def push_type_context : telescope → type_context (list expr)
| Γ := list.mfoldr push_type_context_core [] Γ

private meta def entry.of_local_folder : expr → (list name × telescope) → (list name × telescope)
|  (expr.local_const u p b y) (l,c) := (l ++ [u], (binder.mk p b $ expr.abstract_locals y l) :: c )
| _ _ := undefined_core "entry.of_local_folder"

/-- Convert a list of local constants to a context. -/
meta def of_locals : list expr → telescope
|ls :=  prod.snd $ list.foldr entry.of_local_folder ([],[]) $ ls

meta def pexpr_pis_of_ctxt : telescope → pexpr → pexpr
|[] e := to_pexpr e
|(⟨n,bi,y⟩ :: rest) e :=
    pexpr_pis_of_ctxt rest $ @expr.pi ff n bi (to_pexpr y) $ e

meta def to_cotelescope : telescope → cotelescope := list.reverse

meta instance : has_coe telescope nat := ⟨list.length⟩

meta def length : telescope → nat := list.length

/-- Finds the index of the deepest binder that satisfies the given predicate.
Note that the indexing scheme gives the shallowest binder the index zero. -/
meta def find_index (predicate : binder → Prop) [decidable_pred predicate] : telescope → option ℕ
| [] := none
| (h :: t) := if predicate h then some t.length else find_index t

meta def find_indexes (predicate : binder → Prop) [decidable_pred predicate] : telescope → list ℕ
| [] := []
| (h :: t) := if predicate h then (t.length) :: find_indexes t else find_indexes t

meta def reverse_beta : telescope → expr → expr
| Γ f := Γ.to_lams $ expr.mk_app f $ list.map expr.var $ list.reverse $ list.range Γ.length

meta def count_leading_implicits : telescope → nat
| Γ := list.length $ list.take_while (λ a, ¬ (binder.is_explicit a)) $ list.reverse $ Γ

end telescope

/-- Given a constant function name `f`, infers the type of `f` and returns `f` as a pi_type telescope. -/
meta def tactic.fn_type_of_pis : name → tactic (telescope × expr)
| n := do
    f ← tactic.mk_const n,
    y ← tactic.infer_type f,
    pure $ telescope.of_pis y