import meta.expr .basic

namespace expr

meta def pi_binder : expr → option (binder × expr)
| (pi n bi y b) := some (⟨n,bi,y⟩, b)
| _ := none

meta def lam_binder : expr → option (binder × expr)
| (lam n bi y b) := some (⟨n,bi,y⟩, b)
| _ := none

meta def exists_binder : expr → option (binder × expr)
| `(Exists %%(pi n bi y b)) := some (⟨n,bi,y⟩, b)
| _ := none

meta def exists_conj_binder : expr → tactic (binder × expr)
| `(Exists %%e) := do
  (lam n bi y b) ← tactic.whnf e,
  pure (⟨n,bi,y⟩, b)
| `(%%P ∧ %%Q) := pure (⟨name.anonymous, binder_info.default, P⟩, lift_vars Q 0 1)
| _ := failure

private meta def alt_fold_aux {T} [monad T] [alternative T] {α} (f : ℕ → α → expr → T α) : ℕ → α → expr → T α
| n a e :=
    (do a ← f n a e,
        match e with
        |(app l r) := do a ← alt_fold_aux n a l, alt_fold_aux n a r
        |(lam  _ _ y   b) := do a ← alt_fold_aux n a y, alt_fold_aux (n+1) a b
        |(pi   _ _ y   b) := do a ← alt_fold_aux n a y, alt_fold_aux (n+1) a b
        |(elet _   y v b) := do a ← alt_fold_aux n a y, a ← alt_fold_aux n a v, alt_fold_aux (n+1) a b
        |_ := pure a
        end
    ) <|> pure a

/-- Fold over the expression depth-first, if the folder function fails then that branch is skipped and the parent accumulator value is used.-/
meta def alt_fold {T} [monad T] [alternative T] {α} (f : ℕ → α → expr → T α) : α → expr → T α
:= alt_fold_aux f 0

/-- Check if two expressions have the form `f a b`, `f b a`. -/
meta def is_commute_raw : expr → expr → option expr
| (app (app f1 x1) y1) (app (app f2 x2) y2) := do
    guard $ f1 = f2 ∧ x1 = y2 ∧ y1 = x2, pure f1
| _ _ := none

/-- Get the set of local constants in the given expression. There will be no duplicates in the list. -/
meta def list_locals : expr → list expr
| e := [] <| alt_fold (λ _ acc e, if e.is_local_constant then some (insert e acc) else if e.has_local then some acc else none) [] e

/-- Get the set of metavariables in the given expression. -/
meta def list_mvars : expr → list expr
| e := [] <| alt_fold (λ _ acc e, if e.is_mvar then some (insert e acc) else if e.has_meta_var then some acc else none) [] e

/-- Get the pretty name if the expression is a const, local_const or mvar. -/
meta def as_name : expr → option name
|(local_const unique pretty _ _) := some unique
|(const n _) := some n
|(mvar unique pretty _) := some unique
|_ := none

meta def as_mvar : expr → option (name × name × expr)
|(mvar u p y) := some (u,p,y)
|_ := none

meta def mvar_uniq_name : expr → name
| (mvar u _ _) := u
| _ := default name

meta def mvar_pretty_name : expr → name
| (mvar un pn y) := pn
| _ := inhabited.default name

meta def is_local_const : expr → bool
| (local_const _ _ _ _) := tt
| _ := ff

/-- If the given expression is a delayed abstraction, this will return a list of local-variables that have been delayed and the base expression. -/
meta def as_delayed_abstraction : expr → option (list (name × expr) × expr)
| e := do
    (macro _ xs) ← pure e | none,
    ls ← get_delayed_abstraction_locals e,
    eb :: vs ← pure xs.reverse | none,
    vs ← pure $ list.zip ls vs.reverse,
    pure (vs, eb)

/-- Maneouvre where the occurrences of a specific mvar in a given expression are abstracted.
Assuming the start expression has a free var level of `outer_depth`.  -/
meta def abstract_mvar (outer_depth: nat) : expr → name → expr
| e n := replace e $ λ e depth, if ¬ e.has_meta_var then some $ lift_vars e (depth + outer_depth) 1 else
    match e with
    | (mvar un _ _) :=
        if n = un then some $ var $ depth + outer_depth else none
    | _ := none
    end

/-- `mk_app_some e l` takes an expression which is an expression headed with `l.length` lambdas, and
partially applies the arguments `l` to it and beta-reduces. If an argument in `l` is `none`, then instead, the lambda is preserved.
The resulting expression will be headed with `n` lambdas, where `n` is the number of `none`s in `l`.
It will throw if not called with an expression headed with lambda binders. -/
meta def mk_app_some : expr → list (option expr) → expr
| f [] := f
| (lam n bi y b) ((some a) :: rest) := mk_app_some (instantiate_var b a) rest
| (lam n bi y b) (none :: rest) := lam n bi y $ mk_app_some b rest
| f args := undefined_core "for now mk_app_some assumes expr is a sequence of lambda binders. please η-reduce appropriately before calling this."

meta def app_nth : expr → nat → expr → expr
| (lam _ _ _ b) 0 a := instantiate_var b a
| (lam n bi y b) (nat.succ i) a := lam n bi y $ app_nth b i a
| f 0 a := app f a
| _ _ _ := undefined_core "non-lambda binders not implemented for app_nth. "

meta def has_mvar (e l : expr) : bool :=
ff <| alt_fold (λ _ acc e,
    if acc then none else
    if e.is_mvar ∧ e.mvar_uniq_name = l.mvar_uniq_name then
        some tt
    else if e.has_meta_var
    then some acc
    else none) ff e

meta def to_debug_fmt : expr → format
| (expr.app f g) := format.nest_join_pure "$ " $ [to_debug_fmt f, to_debug_fmt g]
| (expr.var i) := format.nest_join_pure "#" $ [i]
| (expr.local_const un pn bi y) := format.nest_join_pure "lc " $ [to_fmt un, to_fmt pn]
| (expr.mvar un pn _) := format.nest_join_pure "? " $ [to_fmt un, to_fmt pn]
| (expr.lam n bi y b) := format.nest_join_pure "λ " $ [to_fmt n, to_debug_fmt y, to_debug_fmt b]
| (expr.pi n bi y b) := format.nest_join_pure "Π " $ [to_fmt n, to_debug_fmt y, to_debug_fmt b]
| (expr.elet n a y b) := format.nest_join_pure "let " $ [to_fmt n, to_debug_fmt a, to_debug_fmt y, to_debug_fmt b]
| (expr.sort l) := "sort"
| (expr.const n _) := format.nest_join_pure "c " $ [to_fmt n]
| (expr.macro _ _) := "macro"

/-- Is it a pi, lambda, app or elet? -/
meta def is_composite : expr → bool
| (pi _ _ _ _) := tt
| (lam _ _ _ _) := tt
| (app _ _) := tt
| (elet _ _ _ _) := tt
| (macro _ l) := ¬ l.empty
| _ := ff

end expr