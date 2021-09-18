import .expr control.monad.basic .interaction_monad
namespace tactic

open interaction_monad.result

/-- Just assign a metavariable without doing all of the Lean checks. Eg with local context etc. -/
meta def unsafe.assign : expr → expr → tactic unit
| m x := tactic.unsafe.type_context.run $ tactic.unsafe.type_context.assign m x

meta def mk_meta_var' : name → expr → tactic expr
| n e := do unsafe.type_context.run $ unsafe.type_context.mk_mvar n e none

private meta def new_goal : option expr → tactic expr
|none := mk_mvar
|(some e) := mk_meta_var e

/-- `fabricate type s` uses tactic `s` to make an instance of `type`. It saves and restores the goals of the tactic. -/
meta def fabricate (type : option expr) (strat : tactic unit) : tactic expr := do
    new_g ← new_goal type,
    gs ← get_goals,
    set_goals [new_g],
    strat,
    n ← num_goals,
    when (n≠0) (do
        st ← read,
        ppst ← pp st,
        fail $ (to_fmt "fabrication failed, there are unsolved goals:\n") ++ ppst),
    set_goals gs,
    instantiate_mvars new_g

meta def is_success {α} (t : tactic α) : tactic bool := (t *> pure tt) <|> pure ff

/-- Throw away the main goal. -/
meta def ignore : tactic unit := do
    g::gs ← get_goals | pure (),
    set_goals gs

meta def get_exceptional {α} (t : tactic α) : tactic (exceptional α) | s :=
match t s with
|(interaction_monad.result.exception none pos s) :=
    (interaction_monad.result.success (exceptional.exception (λ os, to_fmt "failed")) s)
|(interaction_monad.result.exception (some msg) pos s) :=
    (interaction_monad.result.success (exceptional.exception (λ os, msg())) s)
|(interaction_monad.result.success a s) :=
    (interaction_monad.result.success (exceptional.success a) s)
end

meta def trace_fail {α} : tactic α → tactic α
| t := interaction_monad.trace_fail tactic.trace t

meta def hypothetically {α} (tac : tactic α) : tactic α :=
λ s, match tac s with
|(success a _) := success a s
|(exception ms pos _) := exception ms pos s
end

meta def can_unify (x y : expr) : tactic bool := hypothetically $ ((unify x y) *> pure tt) <|> pure ff

/-- `trace_m x y` is an alias for `(format.join x <$> pp y) >>= trace`. -/
meta def trace_m {α} [has_to_tactic_format α]: string → α → tactic unit
|s a := do ppa ← pp a, trace $ (to_fmt s) ++ ppa

/-- Try all of the tactics in the given list and return the result from
the first one that doesn't fail. Don't do later tactics. -/
meta def try_first {α} : list (tactic α) → tactic α
| []            := failed
| (tac :: tacs) := λ s,
    match tac s with
    | result.success a s' := result.success a s'
    | result.exception e p _ := try_first tacs s
    end

meta def is_class_instance : expr → tactic bool := infer_type >=> tactic.is_class

meta def is_type (e : expr) : tactic bool := do
    T ← infer_type e,
    pure $ (expr.is_sort T ∧ T ≠ `(Prop))

/-- A __term__ here means an expression that is not a Sort or a proof or a typeclass instance.  -/
meta def is_term (e : expr) : tactic bool := do
    T ← infer_type e,
    iscl ← tactic.is_class T,
    ispf ← is_proof e,
    pure $ (¬ expr.is_sort T) && ¬ iscl && ¬ ispf

meta def list_local_const_terms (e : expr) : tactic (list expr)
:= mfilter is_term $ expr.list_locals e

/-- Just assign a metavariable without doing all of the Lean checks. Eg with local context etc. -/
meta def unsafe_assign : expr → expr → tactic unit | m x := unsafe.type_context.run $ unsafe.type_context.assign m x

meta def unsafe_with_local {α} (b : binder) (t : expr → tactic α) : tactic α := do
  h ← unsafe.type_context.run $ unsafe.type_context.push_local b.name b.type b.info,
  a ← t h,
  unsafe.type_context.run $ unsafe.type_context.pop_local,
  pure a

/-- Gets the local context of a given metavariable. -/
meta def get_lctx : expr → tactic _root_.local_context
|mv := unsafe.type_context.run $ unsafe.type_context.get_context mv

meta def is_declared : expr → tactic bool
|mv := unsafe.type_context.run $ unsafe.type_context.is_declared mv

meta def with_goals {α}: list expr → tactic α → tactic α
| gs t := do
    ogs ← get_goals,
    set_goals gs,
    a ← t,
    set_goals ogs,
    pure a

meta def with_state {α} : tactic_state → tactic α → tactic α
| ts t := do
    tso ← read,
    write ts,
    a ← t,
    write tso,
    pure a

end tactic