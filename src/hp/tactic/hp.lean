import control.monad.writer
import .box hp.writeup hp.rewrite

-- meta structure hp.clause : Type :=
-- (c : hp.writeup.Clause)
-- (ts : tactic_state)

meta def hp.writeupresult := list (tactic_state × hp.writeup.act)

@[derive_setters]
meta structure hp.hp_state :=
(ts : tactic_state)
(rt : hp.rule_table)
(labs : hp.labeller)
(writeup : hp.writeupresult)
(b : hp.box)
-- the mvar that the box is going to end up being replaced with.
(result : expr)
(trace : list format := [])
-- these are expressions that should be substituted with the given name
-- when writing up. It is used to prevent "classical.some _" appearing everywhere.
(dont_instantiate : list (expr × name))

open hp

meta def hp (α : Type) := (interaction_monad hp_state) α

open tactic.unsafe undoable_t

namespace hp

section
  local attribute [reducible] hp
  meta instance : monad hp := by apply_instance
  meta instance : monad_state hp_state hp := by apply_instance
  meta instance : alternative hp := by apply_instance
  meta instance has_rt : monad_reader rule_table hp := ⟨hp_state.rt <$> get⟩
  meta instance lift_irs: has_monad_lift tactic (interaction_monad hp_state) := ⟨(λ α x rs,
    match x rs.ts with
    | (interaction_monad.result.success a ts) := (interaction_monad.result.success a $ rs.with_ts ts)
    | (interaction_monad.result.exception msg pos ts) := (interaction_monad.result.exception msg pos (rs.with_ts ts))
    end
  )⟩
  meta instance : has_monad_lift tactic hp := ⟨λ α x, monad_lift x⟩
  meta instance tactic_hp_coe {α : Type} : has_coe (tactic α) (hp α) := ⟨monad_lift⟩
  meta instance : monad_run (interaction_monad hp_state) (hp) := {run := λ α, id}
  meta def has_labeller : monad_state labeller hp := ⟨λ α s, do
    rs ← get,
    (a, labs) ← pure $ s.run rs.labs,
    put $ rs.with_labs labs,
    pure a
  ⟩

  meta def run_simple {α}: hp_state → hp α → option (α)
  | rs r := match r rs with
            |(interaction_monad.result.success a rs) := some (a)
            | _ := none
            end
end

open hp.writeup

meta def hp_state.push_clause : list writeup.act → hp_state → hp_state
| cs rs :=
  hp_state.modify_writeup (list.append $ cs.map $ prod.mk $ rs.ts) rs

-- meta def push_clauses : list writeup.act → hp unit
-- | cs := do
--   --  tactic.trace "push_clauses saving state:",
--   --  tactic.trace_state,
--    s ← get,
--    put $ hp_state.push_clause cs s

/-- add a new expression to the 'don't instantiate list' which is used to make sure that pretty printing of
constants introduced through ∃-elimination appear as pretty variables instead of `classical.some _`. -/
meta def push_dont_instantiate : list (expr × name) → hp unit
| cs := get >>= put ∘ hp_state.modify_dont_instantiate (list.append cs)

meta def no_clauses {α} : hp α → hp α
| r := do
  rs ← get,
  a ← r,
  modify $ hp_state.with_writeup rs.writeup,
  pure a

meta def get_writeup : hp (writeupresult) :=
hp_state.writeup <$> get

meta instance : monad_writer (writeupresult) hp :=
{ tell := λ cs rs, result.success () $ rs.modify_writeup $ list.append cs
, listen := λ α r, pure prod.mk <*> r <*> get_writeup
, pass := λ α r, do (a, f) ← r, modify (hp_state.modify_writeup f), pure a
}

meta def returnopt {m} [alternative m] {α} : option α → m α
| (some a) := pure a | none := failure

meta def hypothetically {α} (r : hp α) : hp α := do
rs ← get,
res ← (some <$> r) <|> pure none,
put rs,
returnopt res

section

meta def has_box : monad_state box hp := ⟨λ α s, do
  r ← get,
  (a,z) ← pure $ state_t.run s $ hp_state.b $ r,
  put $ r.with_b z,
  pure a
⟩

section
  local attribute [instance] has_labeller

  meta def relabel_telescope : telescope → hp telescope
  | bs := labeller.label_telescope bs

  /-- Relabel an unassigned mvar that is not on the box tree yet. -/
  meta def relabel_mvar : expr → option name → hp expr
  | m@(expr.mvar un pn y) (some n) := labeller.rename_meta (expr.mvar un n y)
  | m@(expr.mvar un pn y) (none) := labeller.rename_meta (expr.mvar un name.anonymous y)
  | _ _ := failure

  meta def clear_label : name → hp unit
  | n := labeller.free_label n

  meta def relabel_source : source → hp source
  | s := labeller.relabel_source s

  meta def trace_labeller : hp unit := labeller.trace_label_state

end

open box
section
  local attribute [instance] has_box
  meta def get_box : hp box := get

  meta def mapb (f : box → option box) : hp unit := get >>= returnopt ∘ f >>= put

  meta def run_Z {α}: Z α → box.zipper → hp (α × box.zipper)
  | zz z := do
    (a,z) ← type_context.run $ state_t.run zz z,
    pure (a,z)

  meta def unzip_set_box : box.zipper → hp unit
  | z := do
    ogs ← tactic.get_goals,
    tactic.set_goals [z.1.get_dummy_goal],
    b ← type_context.run $ box.zipper.unzip z,
    tactic.set_goals ogs,
    put b

end

meta def repeat {α} (f : hp α ) : hp (list α) := (do
  a ← f,
  rest ← repeat,
  pure $ a :: rest) <|> pure []

meta def orelse_lazy {α} : hp α → (unit → hp α) → hp α
| a b := a <|> (pure () >>= b)

meta def with_goals {α} : list expr → hp α → hp α
| gs r := do
  ogs ← tactic.get_goals,
  tactic.set_goals gs,
  a ← r,
  tactic.set_goals ogs,
  pure a

meta def trace_fail {α} : hp α → hp α
| r := interaction_monad.trace_fail (monad_lift ∘ tactic.trace) r

meta def trace_result : hp unit := do
  rs ← get,
  r ← tactic.instantiate_mvars $ rs.result,
  b ← assignable.instantiate_mvars $ rs.b,
  b ← pure $ box.clean b,
  tactic.trace b,
  pure ()

open tactic

-- meta def match_target (p : pexpr) : hp (list expr) := do
--   (sum.inl g) ← cursor,
--   t ← infer_type g,
--   p ← pexpr_to_pattern p,
--   tactic.trace p,
--   (ls, es) ← match_pattern p t,
--   pure es

-- meta def replace_target_with_goals (new_goals : list expr) : hp unit := do
--   -- [fixme] goals might be in new contexts, need to add necessary sources if needed!
--   ts ← monad_lift $ list.mmap target.of_goal new_goals,
--   mapz (box.zipper.replace_cursor ts)

-- meta def replace_target (new_targets : list target) : hp unit := do
--   mapz (box.zipper.replace_cursor new_targets)

-- meta def refine_target (assignment : pexpr) : hp (list expr) := do
--   g ← cursor_as_mvar,
--   gs ← get_goals,
--   set_goals [g],
--   tactic.refine assignment,
--   rs ← get_goals,
--   set_goals gs,
--   pure rs

-- meta def push_source (src: source) : hp unit := do
--   mapz (some ∘ zipper.push_source src)

-- meta def go : box.address → hp unit
-- | a := do
--   top,
--   mapz (zipper.down_adr a)

-- meta def assign_target (assignment : expr) : hp unit := do
--   g ← cursor_as_mvar,
--   tactic.unsafe.assign g assignment

meta def trace {α} [has_to_tactic_format α] : α → hp unit
| a := do
  p ← tactic.pp a,
  modify (λ x, hp_state.modify_trace (list.cons p) x)

meta def fail {α β} [has_to_tactic_format α] : α → hp β
| a := do
  p ← tactic.pp a,
  tactic.fail p

meta def create_hp_state : tactic hp_state := do
  rt ← get_equate_rule_table,
  labs ← pure $ inhabited.default hp.labeller,
  [g] ← get_goals,
  ctx ← local_context,
  (init_box) ← box.init ctx g,
  -- ppz ← pp init_box,
  -- make a dummy goal to avoid 'no goals' errors.
  dummy_goal ← tactic.mk_meta_var `(false),
  gs ← get_goals,
  -- set_goals $ gs ++ [dummy_goal],
  ts ← tactic.read,
  writeup ← prod.mk ts <$> writeup.act.Intro <$> (list.mmap hyp.of_expr $ list.reverse $ ctx),
  -- ppgs ← pp gs,
  pure $ { hp_state
         . ts := ts
         , rt := rt
         , labs := labs
         , writeup := [writeup]
         , b := init_box
         , result := g
         , dont_instantiate := []
         }


end

end hp