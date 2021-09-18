import .box .hp .hp_component

open tactic hp tactic.unsafe
namespace hp

meta structure waterfall_command : Type :=
(command_string: string)
(display_name : string := command_string)
(run: rc.action)

/-- Monad for making tactics that act on a hp state at a particular point in the box. -/
meta def ZR := state_t box.zipper hp

section
  local attribute [reducible] ZR
  meta instance ZR.monad: monad ZR := by apply_instance
  meta instance ZR.monad_state: monad_state box.zipper ZR := by apply_instance
  meta instance ZR.alternative: alternative ZR := by apply_instance
  meta instance ZR.monad_lift: has_monad_lift hp ZR := by apply_instance

  meta def Z_lift_ZR {α : Type} : box.Z α → ZR α
  | zz := do
    z ← get,
    dg ← pure z.1.get_dummy_goal,
    ogs ← ⍐ $ tactic.get_goals,
    ⍐ $ tactic.set_goals [dg],
    (a,z) ← monad_lift $ type_context.run $ state_t.run zz z,
    ⍐ $ tactic.set_goals ogs,
    put z,
    pure a

  meta instance ZR.mlZ: has_monad_lift box.Z ZR := ⟨@Z_lift_ZR⟩

  protected meta def ZR.run {α} : ZR α → hp α | zr := do
    -- tactic.trace "ZR.run",
    -- tactic.trace_state,
    ogs ← get_goals,
    b ← hp_state.b <$> get,
    z ← type_context.run $ box.zipper.zip b,
    set_goals [z.1.get_dummy_goal],
    (a,z) ← state_t.run zr z,
    set_goals [z.1.get_dummy_goal],
    -- tactic.trace "\nbefore unzip",
    -- tactic.trace z,
    b ← type_context.run $ (box.zipper.unzip z),
    -- tactic.trace "\nafter unzip",
    -- tactic.trace b,
    set_goals ogs,
    -- tactic.trace b,
    modify $ hp_state.with_b b,
    pure a

  meta instance ZR.mrun : monad_run hp ZR := ⟨@ZR.run⟩
  -- meta def ZR.labs : monad_state labeller ZR :=
  -- ⟨λ α s, monad_lift $ @monad_state.lift _ _ hp.has_labeller _ s⟩
end

namespace ZR

  meta def repeat : ZR unit →  ZR unit
  | a := (a >>= λ _, repeat a) <|> pure ()

  -- meta def with_goals {α: Type} : list expr → ZR α → ZR α
  -- | gs z := do
  --   ogs ← ⍐ tactic.get_goals,
  --   ⍐ $ tactic.set_goals gs,
  --   a ← z,
  --   ⍐ $ tactic.set_goals ogs,
  --   pure a

  /-- Add the given input to the hp state, with some somewhat ad-hoc mutations for getting the format right:
  - if the box includes a `CASE` modifier, then wrap the inputs in a 'Scope' object.
  Assumes that the goals have already been set correctly.
  -/
  meta def push_input : box.path → list writeup.act → hp unit
  | p cs := do
      -- ogs ← ⍐ $ tactic.get_goals,
      -- ⍐ $ tactic.set_goals [z.1.get_dummy_goal],
      rs ← ( get : hp hp_state ),
      xs ← pure
        $ list.olast
        $ list.filter_map (λ x,
          match x with
          | (name.mk_string "CASE" n) := some x
          | _ := none
          end)
        $ box.path.A1_list p,
      cs ← pure $ match xs with
                   | (some n) := list.map (writeup.act.Scope n) $ cs
                   | (none) := cs
                   end,
      rs ← pure $ hp_state.push_clause cs rs,
      put rs,
      -- tactic.set_goals $ ogs,
      pure ()

  -- meta def push_clauses : list writeup.act → ZR unit
  -- | hs := do
  --   z ← get,
  --   ⍐ $ (do
  --     ogs ← (tactic.get_goals : hp _),
  --     tactic.set_goals [z.1.get_dummy_goal],
  --     hp.push_clauses hs,
  --     tactic.set_goals ogs
  --   ),
  --   pure ()

  meta def down : box.coord → ZR unit :=
  ⍐ ∘ box.Z.down

  meta def trace_state : ZR unit := do
    ⍐ $ tactic.trace_state,
    z ← get,
    ⍐ $ tactic.trace z,
    pure ()

  /-- Assuming that the cursor is on a target, this will perform intros on that target. -/
  meta def intros : ZR (list hyp) := do
    box.T s b2 ← ⍐ $ box.Z.cursor,
    t ← pure $ s.type,
    (bs, b) ← pure $ telescope.of_pis t,
    if bs.empty then ⍐ $ fail "nothing to intro" else do
    -- ⍐ $ tactic.trace "\nstart intros:",
    -- ZR.trace_state,
    bs ← ⍐ $ hp.relabel_telescope bs,
    -- (⍐ $ tactic.trace bs),
    b1 ← pure
      $ bs.foldl (λ b x,
        box.I x
        $ box.V { label := x.name
                , value := expr.var 0
                , type  := expr.lift_vars x.type 0 1 }
        $ b)
      $ box.T ⟨s.name, s.info, b⟩
      $ box.R (expr.var 0),
    ⍐ $ box.Z.replace_current_target b1,
    -- c ← ⍐ box.Z.cursor, (⍐ $ tactic.trace c),
    hs : list hyp ← bs.mmap (λ _, ⍐ box.Z.down_IV),
    z@⟨p,_⟩ ← get,
    guard $ ¬ hs.empty,
    -- ⍐ $ tactic.trace "adf",
    ⍐ $ push_input p [(writeup.act.Intro hs.reverse)],
    -- ⍐ $ tactic.trace "end intros\n",
    pure hs

  meta def hypothetically {α} : ZR α → ZR α
  | zr := do
    z ← get,
    (a,_) ← monad_lift $ hp.hypothetically $ state_t.run zr z,
    pure a

  meta def no_clauses {α} : ZR α → ZR α
  | zr := do
    z ← get,
    (a,z) ← monad_lift $ hp.no_clauses $ state_t.run zr z,
    put z,
    pure a

  meta def get_hp_state : ZR hp_state :=
  state_t.lift (get : hp _)

  meta def snapshot : ZR (box.zipper × hp_state) := do
    rs ← get_hp_state,
    z ← get,
    pure (z, rs)

  meta def run_simple {α} : ZR α → (box.zipper × hp_state) → option (α)
  | zz (z,rs) := hp.run_simple rs $ do
    ogs ← get_goals,
    set_goals [z.1.get_dummy_goal],
    (a,z) ← state_t.run zz z,
    set_goals ogs,
    rs ← get,
    pure $ a

  meta def up_clean : ZR unit := do
    -- ⍐ $ tactic.trace "\nupclean",
    ⍐ (box.Z.up_clean)

    -- z ← get,
    -- ⍐ $ tactic.set_goals $ [z.1.get_dummy_goal],
    -- ZR.trace_state


  /-- Unzip the current zipper and set the hp_state's box to be this new box. -/
  meta def commit : ZR unit := do
    -- ⍐ $ tactic.trace "\ncommit",

    z ← get,
    ⍐ $ tactic.set_goals $ [z.1.get_dummy_goal],
    -- ZR.trace_state,

    b ← ⍐ $ type_context.run $ (box.zipper.unzip z),
    -- ⍐ $ tactic.trace "~~~ done commit\n",
    ⍐ $ @modify _ hp _ _ $ hp_state.with_b b,
    pure ()

  meta def goto : box.address → ZR unit | a := ⍐ $ box.Z.goto a

  /-- Cosplit sends an or target to a pair of possible targets using an 𝒪 box. -/
  meta def cosplit : ZR unit := do
    box.T s b ← ⍐ $ box.Z.cursor,
    `(%%A ∨ %%B) ← pure $ s.type, -- [todo] generalise to other constructors later!
    -- ⍐ $ tactic.trace "adf",
    ba ← pure $ box.T ⟨s.name, s.info, A⟩ $ box.R $ expr.mk_app (expr.const `or.inl []) $ [A, B, expr.var 0],
    bb ← pure $ box.T ⟨s.name, s.info, B⟩ $ box.R $ expr.mk_app (expr.const `or.inr []) $ [A, B, expr.var 0],
    b ← pure $ box.O [ba, bb],
    ⍐ $ box.Z.replace_current_target b,
    pure ()

  meta def set_context : ZR unit := do
    z ← get,
    ⍐ $ tactic.set_goals $ [z.1.get_dummy_goal]

end ZR

meta def ZR_to_cmd : ZR string → ZR waterfall_command
| zr := do
  ZR.hypothetically $ (do
    s ← zr,
    z ← get,

    monad_lift $ hp.unzip_set_box z,
    rs ← ZR.get_hp_state,
    pure {
      display_name := s,
      command_string := s,
      run :=  rc.action.new_state rs
    }
  )

@[derive_setters]
meta structure apply_context :=
(type : expr)
(result: expr)

open tactic.unsafe.type_context

meta def apply_fn := apply_context → expr → hp writeup.ApplyTree

meta def get_term_stubs : expr → tactic (list stub) | e := do
  stubs ← pure $ expr.fold e [] (λ x n acc,
    match x with
    | (expr.mvar _ _ _) := x :: acc
    | _ := acc
    end
  ),
  stubs ← stubs.mfilter (λ x, bnot <$> tactic.is_assigned x),
  stubs ← stubs.mfilter (tactic.is_term),
  stubs ← stubs.mmap stub.of_expr,
  pure stubs

meta def apply_match : apply_fn
| ac goal := do
  goal_type ← infer_type goal,
  -- tactic.trace "apply match start: ",
  b ← tactic.infer_type ac.result,
  goal : stub ← pure $ stub.mk goal goal_type, -- [hack] sometimes goal is not a stub, should just be an expr, type bundle.
  -- tactic.trace $ (b, goal_type),
  setters ← get_term_stubs goal_type,
  unify goal_type b (transparency.semireducible) tt,
  setters ← monad_lift $ setters.mfilter stub.is_assigned,
  setters ← monad_lift $ list.mmap (λ s : stub, prod.mk s <$> tactic.instantiate_mvars s) setters,
  -- tactic.trace "apply match found: ",
  -- tactic.trace (b, goal_type),
  r ← instantiate_mvars ac.result,
  with_goals [goal] $ exact r,
  pure $ writeup.ApplyTree.Match ac.result goal setters

meta def apply_and_cases (rec: apply_fn) : apply_fn
| ctx goal := do
  T ← infer_type ctx.result,
  T ← whnf T,
  -- tactic.trace T,
  -- tactic.trace "apply_and_cases start: ",
  `(%%A ∧ %%B) ← pure $ T,
  rl ← mk_app `and.left [ctx.result],
  rr ← mk_app `and.right [ctx.result],
  let run := λ (x y : expr), (do
    xt ← ⍐ $ infer_type x,
    t ← rec {type := xt, result := x} goal,
    s ← source.of_exists `name_goes_here $ y,
    pure $ writeup.ApplyTree.AndElim s t
  ),
  run rl rr <|> run rr rl

-- universes u

meta def apply_ex_cases (rec: apply_fn) : apply_fn
| ctx goal := do
  -- tactic.trace ctx.type,
  `(Exists %%F) ← pure ctx.type,
  -- tactic.trace "\napply_ex_cases",
  -- tactic.trace F,
  (expr.lam n bi y b) ← pure F,
  -- [todo] remove need for classical?
  rv ← to_expr ```(classical.some %%ctx.result),
  rp ← mk_app `classical.some_spec [ctx.result],
  rt ← infer_type rp,
  rt ← tactic.head_beta rt,
  -- ⍐ $ tactic.trace rt,
  -- ogs ← get_goals,
  -- set_goals [goal],
  -- [(n, [rv,rp])] ← cases r ,
  -- [goal] ← get_goals,
--   monad_lift (tactic.trace_state),
  t ← rec {result:=rp, type := rt} goal,
  s ← source.of_exists n rv,
  push_dont_instantiate [(rv,n)],
  -- [todo] fix labelling of item if there is a clash
  pure $ writeup.ApplyTree.ExistsElim s t

meta def apply_pi (rec: apply_fn): apply_fn
| ctx goal := do
  r ← pure $ ctx.result,
  rt ← pure ctx.type,
  (expr.pi n bi y b) ← pure rt,
  -- ⍐ $ tactic.trace "\napply_pi",
  -- ⍐ $ tactic.trace_state,

  lc ← get_lctx goal,
  -- ⍐ $ tactic.trace $ lc.to_list.map expr.local_uniq_name,
  y ← pure y,
  x ← type_context.run $ type_context.mk_mvar n y (some lc), -- todo labelling
  r ← pure $ expr.app r x,
  rt ← infer_type r,
  b ← pure $ expr.instantiate_var b x,
  -- ⍐ $ tactic.trace "rec",
  -- ⍐ $ tactic.trace rt,
  t ← rec {result := r, type := rt} goal,
  with_goals [x] $ (do
    try $ (do
    ip ← is_proof x,
    if ip then do
      a@(expr.local_const un pn bi y) ← infer_type x >>= find_assumption,
      -- tactic.trace_state,
      -- tactic.trace $ ("found assumption", un, pn),
      exact a
    else failure
  ) <|> apply_instance),
  ia ← is_assigned x,
  if ia then do
    xx ← ⍐ $ tactic.instantiate_mvars x,
    -- ⍐ $ tactic.trace $ (x.to_debug_fmt, "is assigned with", xx.to_debug_fmt),
    pure $ writeup.ApplyTree.ApplyAssigned x t
  else do
    it ← is_term x,
    s ← stub.of_expr x,
    s ← assignable.instantiate_mvars s,
    push_dont_instantiate $ [(x, x.mvar_pretty_name)],
    pure $ writeup.ApplyTree.ApplyGoal n bi x t

meta def apply_rec: apply_fn
| acc goal :=
      apply_pi apply_rec acc goal
  <|> apply_match acc goal
  <|> apply_and_cases apply_rec acc goal
  <|> apply_ex_cases apply_rec acc goal

meta structure apply_result :=
(new_targets : list stub)
(new_srcs : list source)

meta def writeup.ApplyTree.sources : writeup.ApplyTree → list source
| (writeup.ApplyTree.Match result goal setters) := []
| (writeup.ApplyTree.ExistsElim value a) := value :: writeup.ApplyTree.sources a
| (writeup.ApplyTree.AndElim value a) := value :: writeup.ApplyTree.sources a
| (writeup.ApplyTree.ApplyAssigned arg a) := writeup.ApplyTree.sources a
| (writeup.ApplyTree.ApplyGoal name bi arg a) := writeup.ApplyTree.sources a

meta def writeup.ApplyTree.targets : writeup.ApplyTree → (tactic (list expr))
| (writeup.ApplyTree.Match result goal setters) := pure []
| (writeup.ApplyTree.ExistsElim value a) := writeup.ApplyTree.targets a
| (writeup.ApplyTree.AndElim value a) := writeup.ApplyTree.targets a
| (writeup.ApplyTree.ApplyAssigned _ a) := writeup.ApplyTree.targets a
| (writeup.ApplyTree.ApplyGoal name bi arg a) := (do
    guardb $ expr.is_mvar arg,
    is_assigned arg >>= guardb ∘ bnot,
    pure (::) <*> pure arg <*> writeup.ApplyTree.targets a)
    <|> writeup.ApplyTree.targets a

/-- Try to apply the given hyp to the cursor.
This essentially does the same thing as tactic.apply
but also projects when it encounters existential quantifiers and conjunctions. -/
meta def apply (h: source) (g : expr) : ZR apply_result := do
  ip ← ⍐ $ is_proof g,
  guard ip,
  -- ogs ← ⍐ $ tactic.get_goals,
  -- ⍐ $ tactic.trace_state,
  -- ⍐ $ tactic.trace "\nbegin apply",
  -- ZR.trace_state,
  -- ⍐ $ tactic.trace_state,
  t ← ⍐ $ apply_rec {result := h.to_expr, type := source.type h} g,
  ⍐ $ clear_label g.mvar_pretty_name,
  new_targets ← ⍐ $ writeup.ApplyTree.targets t,
  -- ⍐ $ tactic.set_goals ogs,
  new_targets ← ⍐ $ new_targets.mmap (λ g, trace_fail $ relabel_mvar g $ some $ expr.mvar_pretty_name g),
  targ_types ←    ⍐ $ new_targets.mmap tactic.infer_type,
  -- ⍐ $ tactic.trace ("waterfall.apply", targ_types),
  new_targets ← ⍐ $ new_targets.mmap tactic.instantiate_mvars,
  new_targets : list stub ← ⍐ $ list.mmap stub.of_expr $ list.reverse $ new_targets,
  t ← ⍐ $ assignable.instantiate_mvars t,
  new_sources ← ⍐ $ list.mmap relabel_source $ writeup.ApplyTree.sources t,
  new_sources ← ⍐ $ assignable.instantiate_mvars new_sources,
  -- replace_target new_targets,
  ⍐ $ box.Z.register_targets new_targets,
  ⍐ $ box.Z.push_sources_high new_sources,
  ⟨p, _⟩ ← get,
  s ← ⍐ $ stub.of_expr g,
  ⍐ $ with_goals (list.map stub.to_expr new_targets) $ ZR.push_input p $ [writeup.act.Apply s h t],
  -- check_done,
  -- ⍐ $ tactic.trace "end apply\n",
  pure ⟨new_targets, new_sources⟩

-- meta def find_apply_first : hp unit := do
--   hs ← get_srcs,
--   list.apick (λ (h : source), do
--     apply h,
--     clean_all
--   ) hs,
--   pure ()

-- meta def induction_folder : list (expr × name × list expr × list (name × expr)) → expr → list expr → box → tactic box
-- | [] result [] b :=

meta def cases_or : ZR unit := do
  box.V s b ← ⍐ $ box.Z.cursor,
  `(%%A ∨ %%B) ← ⍐ $ tactic.whnf $ s.type,
  -- ⍐ $ box.Z.set_cursor b,
  C ← ⍐ $ tactic.unsafe.type_context.run $ box.infer b,
  ah : binder ← pure $ binder.mk s.label binder_info.default A,
  bh : binder ← pure $ binder.mk s.label binder_info.default B,
  rb ← pure
    $ box.A (box.IV ah b) ⟨`or.inl.CASE, binder_info.default, binder.to_pi ah C⟩
    $ box.A (box.IV bh b) ⟨`or.inr.CASE, binder_info.default, binder.to_pi bh C⟩
    $ box.R $ expr.mk_app (expr.const `or.rec []) [A, B, C, expr.var 1, expr.var 0, s.value],
  ⍐ $ box.Z.set_cursor rb,
  z  ← get,
  ⍐ $ ZR.push_input (z.get_path) $ [writeup.act.Cases [ah, bh]],
  pure ()

/-- Split a source `h : A ∧ B` to `h₁ : A` and `h₂ : B`. -/
meta def cases_and : ZR unit := do
  box.V s b ← ⍐ $ box.Z.cursor,
  `(%%A ∧ %%B) ← ⍐ $ tactic.whnf $ s.type,
  -- [todo] add labeller system
  e1 ← ⍐ $ to_expr ```(and.left %%s.value),
  e2 ← ⍐ $ to_expr ```(and.right %%s.value),
  s1 ← pure $ {source. label := s.label ++ `l, value := e1, type := A},
  s2 ← pure $ {source. label := s.label ++ `r, value := e2, type := B},
  ⍐ $ box.Z.set_cursor $ box.V s1 $ box.V s2 $ b,
  pure ()

/- This is _way_ too complicated. -/
-- meta def induction : ZR unit := do
--   s ← ⍐ $ box.Z.down_V,
--   b ← ⍐ $ box.Z.cursor,
--   e ← ⍐ $ tactic.get_env,
--   (expr.const n _) ← pure $ expr.get_app_fn $ s.type,
--   guard (environment.is_inductive e n),
--   some rec_name ← pure $ e.recursor_of n,
--   ctors ← pure $ environment.constructors_of e n,
--   box_result_type ← ⍐ $ tactic.unsafe.type_context.run $ box.infer b,
--   x ← ⍐ $ (do
--     ogs ← tactic.get_goals,
--     v ← mk_meta_var box_result_type,
--     set_goals [v],
--     -- tactic.applyc rec_name,
--     cs ← tactic.induction s.value,
--     gs ← get_goals,
--     guard (gs.length = cs.length),
--     v ← instantiate_mvars v,
--     gcs ← pure $ list.zip gs cs,
--     (f, ls) ← gcs.mfoldr (λ ⟨g, n, hs, _⟩ (v : expr × list telescope), do
--       expr.app f a ← pure v.1,
--       (bs, a) ← telescope.of_n_lams a hs.length,
--       pure (f, bs :: v.2)
--     ) (v,[]),
--     rbox ← pure $ box.R $ expr.mk_app f $ list.map expr.var $ list.tail $ list.scanr (λ _, nat.succ) 0 gcs,
--     lgcs ← pure $ list.zip ls gcs,
--     side_boxes ← lgcs.mmap (λ ⟨Γ, g, n, hs, _⟩, do
--       b ← assignable.kabstract b s.value,

--     ),

--     final_box ← lgcs.mfoldr (λ ⟨Γ,g,n,hs,_⟩ b2, do
--     ) rbox,
--     tactic.set_goals ogs,
--     pure v
--     ),
--   pure ()


  -- ① find the induction principle for s;
  -- this should have the form `rec C ..(Π ..xs ..hs, C $ T ..xs) x`
  /- There will be loads of really tricky cases where we can't easily
  infer the motive since it is applied to many targets
  simultaneously. But we will ignore this issue for now. -/
  -- ② take the child box, duplicate it for each constructor
  -- ③ add these boxes to each case, add the additional constructors.

  /- Idea; is there a clever way to do this using the built in induction system? I can't see it. -/

-- meta def wfcmd_of_ZR : ZR string → ZR waterfall_command := do


-- meta def wfcmd_of_hp (r : box.zipper → hp string) : hp waterfall_command := do
--   t ← hp.cursor_as_mvar,
--   hp.hypothetically $ (do
--       label ← r,
--       clean_all,
--       rs ← get,
--       pure {display_name := label, command_string := label, run := put rs *> pure ()}
--   )

-- meta def wfcmd_of_tactic (r : tactic string) : hp waterfall_command :=
--   wfcmd_of_hp (do
--     t ← hp.cursor_as_stub,
--     ogs ← tactic.get_goals,
--     tactic.set_goals [t],
--     y ← infer_type t,
--     depends ← get_term_stubs y,
--     label ← r,
--     setters ← ⍐ $ depends.mfilter stub.is_assigned >>= list.mmap (λ s, prod.mk s <$> tactic.instantiate_mvars s),
--     t' ← instantiate_mvars t,
--     -- [todo] also generate a clause here: eg
--     -- "by %%label, we have / suffices to show "
--     ngs ← tactic.get_goals,
--     nts ← ⍐ $ list.mmap box.target.of_goal ngs, -- [todo] some work needed here to make sure that sources etc are correctly added
--     rs ← ngs.mfoldr (λ t, pure ∘ (writeup.ApplyTree.ApplyGoal (option.iget $ expr.as_name t) binder_info.default t))
--       $ writeup.ApplyTree.Match t' t setters,
--     hp.replace_target nts,
--     push_clauses $ singleton $ writeup.Clause.TargetTactic ⟨t,y⟩ label rs,
--     tactic.set_goals ogs,
--     check_done,
--     pure label
--   )

-- meta def refl_cmd := wfcmd_of_tactic (reflexivity *> pure "reflexivity") -- [todo] add 'reflexivity as the reason

meta def applycmds : ZR (list waterfall_command) := (ZR.hypothetically $ do
  g ← ⍐ $ box.Z.down_stub,
  hs ← ⍐ box.Z.source_list,
  xs : list (source × hp_state) ← list.achoose (λ (h: source), ZR.hypothetically $ do
    apply h g,
    ZR.commit,
    rs ← ZR.get_hp_state,
    pure (h, rs)
  ) hs,
  pure $ xs.map (λ ⟨h, rs⟩,
    let str := "apply " ++ to_string h.label in
    { display_name := str,
      command_string := str,
      run := rc.action.new_state $ rs
    }
  )) <|> pure []

meta def split_target : stub → ZR apply_result | g := do
  -- ogs ← monad_lift $ tactic.get_goals,
  -- ⍐ $ set_goals [g],
  [c] ← ⍐ $ infer_type g >>= get_constructors_for,
  c ← ⍐ $ mk_const c,
  s ← ⍐ $ source.of_expr `split c,
  res ← ZR.no_clauses $ apply s g,
  -- ⍐ $ tactic.trace ("split_target", g.type),
  -- monad_lift $ set_goals ogs,
  ZR.commit,
  -- ZR.trace_state,
  pure res

meta def split_conj_cmd : ZR string := do
  g ← ⍐ $ box.Z.down_stub,
  y ← ⍐ $ infer_type g,
  yy ← ⍐ $ tactic.instantiate_mvars y,
  -- ZR.trace_state,
  `(%%A ∧ %%B) ← pure y,
  r ← split_target g,
  -- ⍐ $ trace_m "split_conj_cmd" $ (A,B),
  [p, v] ← pure r.new_targets,
  ⟨path, _⟩ ← get,
  ⍐ $ ZR.push_input path $ singleton $ writeup.act.Andi v p,
  pure "split"

meta def split_exists : ZR string := do
  g ← ⍐ $ box.Z.down_stub,
  `(Exists %%A) ← ⍐ $ infer_type g,
  r ← split_target g,
  [p, v] ← pure r.new_targets,
  ⟨path, _⟩ ← get,
  ⍐ $ ZR.push_input path $ singleton $ writeup.act.Existsi v p,
  ⍐ $ box.Z.up,
  pure "split"

/-- A heuristic that some expression is only worth 'expanding'
(ie dsimping) if the expansion results in a logical formula. -/
meta def is_weak_expandable : expr → tactic bool
| `(set %%X) := pure ff
| e := do
  e ← tactic.whnf e,
  match e with
  | (expr.pi _ _ _ _) := pure tt
  | `(%%A ∨ %%B) := pure tt
  | `(%%A ∧ %%B) := pure tt
  | `(Exists %%P) := pure tt
  | _ := pure ff
  end

meta def expand_target : ZR string := do
  (p, box.T ⟨n, bi, y⟩ b) ← get,
  y2 ← ⍐ $ tactic.whnf y,
  guard (y ≠ y2),
  ⍐ $ alternative.mguard (is_weak_expandable y),
  put (p, box.T ⟨n, bi, y2⟩ b),
  -- ⍐ $ push_clauses [], -- todo -- push a reason for the expansion.
  pure "expand"

meta def expand_source : ZR string := do
  -- ⍐ $ tactic.trace "expanding source",
  (p, box.V s b) ← get,
  -- ⍐ $ tactic.trace $ s.type.to_string,
  -- y2 ← ⍐ $ tactic.dunfold_head $ s.type,
  y2 ← ⍐ $ tactic.whnf s.type,
  -- ⍐ $ tactic.trace $ y2.to_string,
  guard (s.type ≠ y2),
  ⍐ $ alternative.mguard (is_weak_expandable s.type),
  put (p, box.V {type := y2, ..s} b),
  -- ⟨path, _⟩ ← get,
  -- ⍐ $ push_clauses [],
  pure "expand"

open widget

-- meta def split_exists_cmd : hp waterfall_command := wfcmd_of_hp $ split_exists

meta def unroll_once : ZR unit :=
  (do
    -- ZR.trace_state,
    (
      (ZR.intros *> pure ())
      <|> (expand_target *> pure ())
      <|> (split_exists *> pure())
      <|> (split_conj_cmd *> pure ())
    ),
    pure ()
  )

meta def unroll : ZR unit := do
    (ZR.intros *> pure "" <|> split_exists <|> split_conj_cmd),
    ZR.repeat (do
      ⍐ $ box.Z.goto_last_target,
      unroll_once
    )

meta def get_commands : ZR (list waterfall_command)
:= do
  -- ⍐ $ tactic.trace "get_commands!",
  -- ZR.trace_state,
  aps ← applycmds,
  cs ← list.achoose id $
    [
      -- ZR_to_cmd (ZR.intros *> pure "intros")
    -- , split_conj_cmd
    -- , ZR_to_cmd (split_exists)
    -- , ZR_to_cmd (split_conj_cmd)
      ZR_to_cmd (unroll *> pure "unroll")
    -- , refl_cmd
    , ZR_to_cmd expand_target
    , ZR_to_cmd expand_source
    ]
    ++ (pure <$> aps),
  -- ⍐ $ tactic.trace "got targets",
  pure cs

-- meta def fail_trace : hp unit := do
--   trace "I failed",
--   pure (),
--   fail "this is the failure message"

-- meta def do_nothing : hp unit := pure ()

end hp