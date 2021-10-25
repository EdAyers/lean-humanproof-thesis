import basic .hp .hp_component .view

namespace hp

open interaction_monad.result widget rc
-- #check create_hp_state
-- meta def rc.run_to_tc {π α} [has_should_update π]: rc π α → tc π α
-- | rr :=
--   component.with_should_update (λ ⟨ts₁,p₁⟩ ⟨ts₂, p₂⟩, (should_update p₁ p₂))
--   $ component.with_state
  -- $ component.with_state

  -- $ component.stateful β (result hp_state σ)
  -- (λ ⟨ts,p⟩ last,
  --   match last with
  --   | none := match create_hp_state ts with
  --             | (success rs _) := let r := run $ i p none in r rs
  --             | (exception _ _ ts) := undefined_core "rc.run_to_tc create_hp_state failed" -- [hack]
  --             end
  --   | some (success s rs) := let r := run $  i p (some s) in r rs
  --   | some (exception _ _ rs) := let r := run $ i p none  in r rs
  --   end
  -- ) (λ ⟨_,p⟩ s b,
  --   match s with
  --   | (success s rs) := let r := run $ u p s b in let r := r rs in (prod.fst <$> r,result.get r >>= prod.snd)
  --   | x := (x,none)
  --   end
  -- ) (λ ⟨_,p⟩ s,
  --   match s with
  --   | (success s rs) := let r := run $ v p s in let r := r rs in ["error occurred"] <| r.get
  --   | (exception msg _ rs) := ["error: ", show_html msg]
  --   end
  -- )

-- meta def rc.run : rc unit string → component tactic_state string
-- | r := tc.to_component $ rc.run_to_tc r

open tactic
meta def rt_run {α : Type}: hp α → tactic α
| r := do
  rs ← create_hp_state,
  let r := (run r),
  match r rs with
  | (result.success a rs) := do
    tactic.write rs.ts,
    (result, gs) ← tactic.unsafe.type_context.run $ box.all_targets rs.b,
    -- tactic.trace result,
    tactic.unsafe.assign rs.result result,
    tactic.set_goals gs,
    pure a
  | (result.exception m p rs) := (λ _, result.exception m p rs.ts)
  end

meta def rt_run_inst: monad_run tactic hp :=
{run := @rt_run}


meta def step {α : Type} (m : hp α) : hp unit :=
m >> pure ()

-- /- istep is used to make an interactive thingy.  -/
-- meta def istep_core {σ τ α : Type} (line0 col0 line col : nat) (t : state_t σ (interaction_monad τ) α) : state_t σ (interaction_monad τ) unit :=
-- ⟨λ v s,
--   match (@scope_trace _ line col (λ _, t.run v s)) with
--   | (success ⟨a,v⟩ s') := success ((),v) s'
--   | (exception (some msg) p s') := exception (some msg) (some ⟨line, col ⟩) s'
--   | (exception none p s') := silent_fail s'
--   end
-- ⟩
meta def istep_core {α : Type} (line0 col0 line col : nat) (t : hp α) : hp unit :=
-- @monad_lift (interaction_monad hp_state) hp _ unit $
λ v : hp_state,
  match ((@scope_trace _ line col (λ _, let r := (run t) in r v)) : interaction_monad.result hp_state α) with
  | (success a s') := success () s'
  | (exception (some msg) p s') := exception (some msg) (some ⟨line, col ⟩) s'
  | (exception none p s') := silent_fail s'
  end

meta def istep {α : Type} (line0 col0 line col ast : nat) (r : hp α) : hp unit :=
istep_core line0 col0 line col r

meta instance : interactive.executor hp :=
{ config_type := nat,
  execute_with := λ n tac, rt_run tac
}

meta def main (rs : hp_state) : component tactic_state empty :=
component.with_should_update (λ _ _, tt)
$ component.stateful string unit
(λ _ _, ⟨⟩)
(λ _ _ _, (⟨⟩, none))
(λ _ _, html.of_component rs app)

meta def save_info (p : pos) : hp unit := do
  v ← get,
  monad_lift $ tactic.save_widget p $ main v,
  pure ()


open tactic.unsafe

meta def first {α} : ZR α → hp α
| zr := do
  rs ← get,
  b ← pure $ rs.b,
  adrs ← pure $ box.target_addresses b,
  adrs.mfirst (λ adr, ZR.run $ do
      ZR.goto adr,
      zr
  )

namespace interactive

meta def trace_box : hp unit := do
  rs ← get,
  ⍐ $ tactic.trace rs.b,
  pure ()

meta def trace_writeup : hp unit := do
  rs ← get,
  r ← monad_lift $ writeup.write rs.dont_instantiate rs.writeup.reverse,
  -- [todo] tostring the html?
  pure ()

meta def try_targets_with_name {α} : name → ZR α → ZR α | n z := do
  ⟨_,b⟩ ← get,
  adrs ← pure $ box.find_targets_with_name n b,
  adrs.mfirst (λ a, do
    ⍐ $ box.Z.down_adr a,
    z
  )

meta def try_with_name {α} : name → ZR α → ZR α | n z := do
  ⟨_, b⟩ ← get,
  adrs ← pure $ box.find_with_name n b,
  adrs.mfirst (λ a, do
    ⍐ $ box.Z.down_adr a,
    z
  )


meta def try_all_targets {α} : ZR α → ZR α | z := do
  adrs ← ⍐ $ box.Z.prop_goal_addresses,
  adrs.mfirst (λ a, do
    ⍐ $ box.Z.down_adr a,
    z
  )

meta def intros : hp unit :=
  ZR.run $ try_all_targets $ ZR.intros *> pure ()

meta def cosplit : hp unit :=
  ZR.run $ try_all_targets $ ZR.cosplit

meta def split : hp unit := ZR.run $ try_all_targets $ (split_conj_cmd <|> split_exists) *> pure ()

meta def trace_commands_at (n : name) : hp unit := do
  ZR.run (do
    ⍐ $ box.Z.goto_name n,
    cs ← get_commands,
    ⍐ $ tactic.trace $ waterfall_command.display_name <$> cs,
    pure ()
  )

@[derive has_reflect, derive has_to_tactic_format]
meta inductive source_loc
| of_name (n : name)
| of_type_pexpr (t : pexpr)
| just_pexpr (e : pexpr)

@[reducible]
meta def target_loc := option name


open lean.parser

meta def surround {α} (l r : string) : lean.parser α → lean.parser α
| p := tk l *> p <* tk r

meta def parse_source_loc : lean.parser (source_loc) :=
  (pure source_loc.of_name <*> ident)
  -- <|> surround "‹" "›" (pure source_loc.of_type_pexpr <*> lean.parser.pexpr std.prec.max tt)
  <|> ((pure source_loc.just_pexpr) <*> interactive.types.texpr)

meta def goto_source_from_loc : source_loc → box.Z unit
| (source_loc.of_name n) := do
  b ← box.Z.cursor,
  a ← returnopt $ box.find_source (λ Γ s, s.label = n) b,
  box.Z.goto a
| _ := notimpl

meta def get_source_from_loc : source_loc → list source → tactic (list source)
| (source_loc.of_name n) ss := singleton <$> (alternative.returnopt $ ss.find (λ x, x.label = n))
| (source_loc.of_type_pexpr p) ss := do
  T ← tactic.to_expr p tt ff,
  ss.mfilter (λ s, tactic.can_unify s.type T)
| (source_loc.just_pexpr p) _ := do
  x ← tactic.to_expr p tt ff,

  s ← source.of_lemma x,
  pure [s]

meta def parse_targ_loc : lean.parser target_loc :=
  (optional (tk "at") *> pure some <*> ident) <|> pure none

meta def try_loc {α} : option name → ZR α → ZR α
| none z := try_all_targets z
| (some n) z := try_with_name n z

meta def apply (s : interactive.parse parse_source_loc) (t : interactive.parse parse_targ_loc) : hp unit :=
  ZR.run $ try_loc t (do
    ZR.set_context,
    g ← ⍐ $ box.Z.down_stub,
    ss ← ⍐ $ box.Z.source_list,
    ss ← ⍐ $ get_source_from_loc s ss,
    ss.mfirst (λ s, do
      hp.apply s g,
      ZR.commit
    ))

meta def cases (s : interactive.parse parse_source_loc) : hp unit :=
ZR.run (do
  ⍐ $ goto_source_from_loc s,
  cases_or <|> cases_and
)

meta def expand (s : interactive.parse parse_targ_loc) : hp unit :=
ZR.run $ try_loc s ( (expand_target <|> expand_source) *> pure ())

meta def unroll (s : interactive.parse parse_targ_loc) : hp unit :=
ZR.run $ try_loc s $ hp.unroll

end interactive
end hp
-- set_option pp.all true
open hp
set_option trace.app_builder true
-- example {P: nat → nat → Prop} : Π (p : ∀ y, ∃ x, P y x), ∃ z, P 0 z :=
-- begin [hp]
--   -- (ZR.run (do (⍐ box.Z.first_goal) *> get_target_commands >>= (list.mmap $ pure ∘ waterfall_command.display_name))) >>= ⍐ ∘ tactic.trace,
--   intros,
--   -- (ZR.run (⍐ (box.Z.intros) *> get_target_commands *> ZR.trace_state)),
--   split,
--   apply_first `p,
--   -- (ZR.run (do ((⍐ box.Z.first_goal) *> (⍐ box.Z.next)) *> get_target_commands >>= (list.mmap $ pure ∘ waterfall_command.display_name))) >>= ⍐ ∘ tactic.trace,
-- end