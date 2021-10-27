import .data .cpc
open tactic
namespace hp

namespace writeup

open act

open Statement

namespace Statement

/-- The empty statement. -/
meta def True : Statement := Statement.And []

meta def as_And : Statement → option (list Statement)
| (Statement.And l) := some l | _ := none

/-- Returns tt if the statment is just the trivial statement.-/
meta def is_True : Statement → bool
| (Statement.And []) := tt | _ := ff

/-- ⋀ a list of statements -/
meta def meet : list Statement → Statement
| ss := Statement.And $ list.collect (λ x,
      match x with
      | (Statement.And l) := l
      | x := [x]
      end)  $ ss

meta def conj : Statement → Statement → Statement
| a b := meet [a,b]

/- Now define a set of mutually recursive definitions for normalising a statement before rendering.
This is purely heuristic to make statements read a little nicer.
Here is what it does:

- `imp`
  * uncurries pi telescopes. ie `(A → B → C) ⟼ (A × B → C)`
  * In the case that `→ T` where `T` is a term, write this as 'whenever'.

- `bake bs cpcs` transforms bs to a set of cpcs and then condenses them with the existing cpcs list.
 -/
meta mutual def imp, bake, fa, ex, for_some, ofProp

with imp : Statement → Statement → Statement
| a (Implies p c) := Implies (Statement.meet [a, p]) c
| a (Whenever p c) := Whenever (Statement.meet [a, p]) c
| a b@(TermStatement x) := Whenever a b -- heuristic for making sentence flow
| a b := Implies a b

with bake : list expr → cpcs → tactic (cpcs × list Statement)
| binders bs := do
      ⟨cpcs, conds⟩ ← to_cpcs tt binders,
      conds ← list.mmap (infer_type >=> ofProp) $ conds,
      cpcs ← condense $ cpcs ++ bs,
      pure $ (cpcs, conds)

with fa : list expr → Statement → tactic Statement
| binders s := do
      (bs, s) ←
            match s with
            | (Statement.Forall bs s) := pure (bs, s)
            | _ := pure ([], s)
            end,
      (cpcs, conds) ← bake binders bs,
      concl ← pure $ list.foldr imp s conds,
      pure $ Forall cpcs concl

with ex : list expr → Statement → tactic Statement
| binders s := do
      (bs, s) ←
            match s with
            | (Statement.Exists bs s) := pure (bs, s)
            | _ := pure ([], s)
            end,
      (cpcs, conds) ← bake binders bs,
      concl ← pure $ meet $ conds ++ [s],
      pure $ Exists cpcs concl

with for_some : list expr → Statement → tactic Statement
| binders s := do
      (bs, s, w) ←
            match s with
            | (Statement.ForSome s bs w) := pure (bs, s, w)
            | _ := pure ([], s, Statement.True)
            end,
      (cpcs, conds) ← bake binders bs,
      concl ← pure s,
      pure $ Statement.ForSome concl cpcs $ meet conds

/- Sends a proposition to a natural language statement of that proposition. -/
with ofProp : expr → tactic Statement
| P := do
      match P with
      | P@(expr.pi pn _ y b) := do
            if (expr.is_arrow P) then
                  pure imp
                  <*> (ofProp y)
                  <*> (ofProp $ expr.instantiate_var b $ mk_local pn)
            else do
                  (bs, b) ← pure $ telescope.of_pis P,
                  ls ← telescope.to_locals bs,
                  b ← pure $ b.instantiate_vars $ ls,
                  ofProp b >>= fa ls.reverse
      | P@`(_root_.Exists %%Q) := do
                  (bs, b) ← telescope.of_exists_conj P,
                  -- tactic.trace "hello from Exists",
                  -- tactic.trace $ list.map binder.name bs,
                  guard $ bs.length > 0,
                  ls ← telescope.to_locals bs,
                  b ← pure $ b.instantiate_vars $ ls,
                  ofProp b >>= ex ls.reverse
      | `(%%P ∧ %%Q) := do
                  pure Statement.conj <*> ofProp P <*> ofProp Q
      | P := (do
            wt ← get_writeup_table,
            -- trace_m "ofProp: " $ P,
            cpc ← cpc.of_prop wt P,
            pure $ Statement.CPC cpc
      ) <|> (get_prop_writeup P) <|> (pure $ Statement.TermStatement P)
      end

meta def suff : list expr → Statement → tactic Statement
| binders s := do
      (bs, s) ← pure $ match s with
                        | (Statement.Suffices bs s) := (bs, s)
                        | s := ([], s)
                        end,
      (bs, conds) ← bake binders bs,
      concl ← pure $ meet $ conds ++ [s],
      pure $ Statement.Suffices bs concl

-- meta def ofProp : expr → tactic Statement
-- | e := do
--   t ← tactic.infer_type e,
--   pure $ TermStatement t -- [todo] do some preprocessing

end Statement

open Sentence

@[derive_prisms, derive has_to_tactic_format]
meta inductive ReasonReduction
| LongReason : list Sentence → ReasonReduction
| ShortReason : Reason → ReasonReduction
| Immediate : ReasonReduction
| Omit

open Reason ReasonReduction

meta def Reason.reduce : SourceReason → tactic ReasonReduction
| (SourceReason.Assumption n e y) := do
      -- trace_m "Reason.reduce: " $ y,
      s ← Statement.ofProp y,
      -- trace_m "Reason.reduce: " $ y,
      pure $ ReasonReduction.ShortReason $ Reason.Since $ s
| (SourceReason.Lemma h) := pure Immediate
| (SourceReason.Since r) := do s ← Statement.ofProp r, pure $ ReasonReduction.ShortReason $ Reason.Since s
| (SourceReason.Forward implication premiss) := undefined_core "not implemented Reason.reduce"
| (SourceReason.And r1 r2) := undefined_core "not implemented Reason.reduce"
| (SourceReason.ConjElim conj index) := undefined_core "not implemented Reason.reduce"
| SourceReason.Omit := pure Omit
| (SourceReason.ExpandLocal r src) := undefined_core "not implemented Reason.reduce"
| (SourceReason.Setting r setters) :=
      pure $ ShortReason $ Reason.BySetting $ setters

open list_parser

meta def tact := tactic_state × act

/-- Try to parse an input and also set the stored tactic state. -/
meta def ctest {γ} (f : act → option γ) : list_parser tact tactic γ := do
  (ts,c) ← list_parser.take,
  match f c with
  | (none) := throw "match failed"
  | (some g) := do
      ⍐ $ tactic.write ts,
      pure g
  end

meta def parse_take : list_parser tact tactic (list Sentence) := do
  takes ← (ctest act.as_Intro),
  takes ← pure $ takes.reverse,
--   monad_lift $ tactic.trace "\nparse_take",
--   monad_lift $ tactic.local_context >>= tactic.trace,
  takes ← pure $ list.map hyp.to_expr $ takes,
  new_vars ← ⍐ $ list.mfilter (λ x, pure bor <*> is_term x <*> is_type x) $ takes,
  (cpcs, other_hyps) ← ⍐ $ to_cpcs ff $ takes,
--   monad_lift $ tactic.trace "~~~ parse_take ~~~ ",
--   monad_lift $ tactic.trace $ list.map expr.local_type $ new_vars,
--   monad_lift $ tactic.trace $ list.map expr.local_type $ cpcs.bind cpc.subjects,
  (new_var_cpcs, cpcs) ← cpc.partition_subjects (λ x, monad_lift $ list.msome (λ y, alternative.is_ok $ tactic.is_def_eq x y) new_vars) cpcs,
--   monad_lift $ tactic.trace $ new_var_cpcs,
--   monad_lift $ tactic.trace $ cpcs,
  (new_var_cpcs, cpcs₂) ← pure $ first_mentions ([],[]) new_var_cpcs,
  other_hyps_smt ← monad_lift $ (Statement.meet <$> list.mmap (infer_type >=> Statement.ofProp) other_hyps),
  cpc_smt ← pure $ Statement.meet $  list.map Statement.CPC $ cpcs ++ cpcs₂,
  rest ← pure $ Statement.meet [cpc_smt, other_hyps_smt],
--   monad_lift $ tactic.trace_m "parse_take: " (intros, rest, rest₂, rest₃),
--   monad_lift $ tactic.trace "end parse_take\n",
  pure [Sentence.Let new_var_cpcs rest]

meta def parse_choose : list_parser tact tactic (list Sentence) := do
  cs ← pure list.cons <*> ctest as_Existsi <*> list_parser.many (ctest as_Existsi <|> ctest as_Andi),
  guard (¬cs.empty),
  ⟨vs, ps⟩ ← pure $ list.unzip cs,
--   monad_lift $ tactic.trace "parse_choose",
--   monad_lift $ tactic.trace $ list.map stub.type $ vs,
--   monad_lift $ tactic.trace ps,
  -- we only need the last p.
  g ← returnopt $ list.olast ps,
  prop ← monad_lift $ Statement.ofProp g.type,
  (cpcs, rest) ← monad_lift $ to_cpcs tt $ stub.to_expr <$> vs,
  rest ← ⍐ $ list.mmap Statement.ofProp $ rest,
  s ← pure $ Sentence.WeMustChoose cpcs $ Statement.And $ rest ++ [prop],
  pure [s]

open tactic

-- meta def Apply_list : ApplyTree → (list (expr) × ApplyTree)
-- | (ApplyTree.Apply name bi arg a) :=  let (rest, x) := Apply_list a in ((arg)::rest, x)
-- | a := ([], a)

meta def ApplyTree.collect_goals : ApplyTree → tactic (list expr × ApplyTree)
| (ApplyTree.ApplyGoal _ _ g a) := do ⟨gs, a⟩ ← ApplyTree.collect_goals a, pure $ (g::gs, a)
| (ApplyTree.ApplyAssigned _ a) := ApplyTree.collect_goals a
| a := pure ([],a)

meta def ApplyTree.collect_goals_and_assumptions : ApplyTree → tactic (list expr × list expr × ApplyTree)
| (ApplyTree.ApplyGoal _ _ g a) := do (gs, asms, a) ← ApplyTree.collect_goals_and_assumptions a, pure $ (g::gs, asms, a)
| (ApplyTree.ApplyAssigned e a) := do
      -- only keep the proposition assumptions:
      ip ← is_proof e,
      if ip then do
            (gs, asms, a) ← ApplyTree.collect_goals_and_assumptions a,
            pure (gs, e :: asms, a)
      else
            ApplyTree.collect_goals_and_assumptions a
| a := pure ([],[], a)

meta def ApplyTree.collect_srcs : ApplyTree → tactic (list source × ApplyTree)
| (ApplyTree.AndElim s a) := do ⟨gs, a⟩ ← ApplyTree.collect_srcs a, pure $ (s::gs, a)
| (ApplyTree.ExistsElim s a) := do ⟨gs, a⟩ ← ApplyTree.collect_srcs a, pure $ (s::gs, a)
| (ApplyTree.ApplyAssigned _ a) := ApplyTree.collect_srcs a
| a := pure ([],a)

meta def ApplyTree.get_results : ApplyTree →  (list expr)
| (ApplyTree.Match result _ _) := [result]
| (ApplyTree.ExistsElim s a) := ApplyTree.get_results a
| (ApplyTree.ApplyAssigned s a) := ApplyTree.get_results a
| (ApplyTree.ApplyGoal _ _ _ a) := ApplyTree.get_results a
| (ApplyTree.AndElim s a) := ApplyTree.get_results a



meta def result_to_reason : expr → tactic Reason
| e := do
      f ← pure $ expr.get_app_fn e,
      args ← pure $ expr.get_app_args e,
      T ← infer_type f,
      (prems, conc) ← pure $ telescope.of_pis T,
      n ← pure $ telescope.count_leading_implicits prems,
      (f, args) ← pure $ expr.get_app_fn_args_n (prems.length - n + 1) e,
      T ← infer_type f,
      smt ← Statement.ofProp T,
      -- trace_m "result_to_reason: " $ (f, args, smt),
      pure $ Reason.Since smt

meta def ApplyTree.get_source_reason : ApplyTree → tactic Reason
| a := do
      (list.cons result _) ← pure $ ApplyTree.get_results a,
      reason ← (result_to_reason result) <|> (pure Reason.Omit),
      -- trace_m "ApplyTree.get_source_reason" $ reason,
      pure reason


meta def ApplyTree.mk_root : ApplyTree → tactic Statement
| a := do
      (gs, asms,  ApplyTree.Match result goal setters) ← ApplyTree.collect_goals_and_assumptions a,
      if gs.empty then do
            -- in this case, the application was successful and there are no more goals to match.
            gt ← pure $ goal.type,
            s ← Statement.ofProp gt,
            r ← pure $ if setters.empty then Reason.Omit else Reason.BySetting setters,
            -- trace_m "ApplyTree.mk_root" $ setters,
            if asms.empty then
                  pure $ Statement.By (Statement.WeAreDone) r
            else
                  pure $ Statement.By (Statement.Have s) r
      else do
            -- in this case, there are new goals introduced.
            gt ← pure $ goal.type,
            r ← pure $ if setters.empty then Reason.Omit else Reason.BySetting setters,
            -- trace_m "mk_root: " $ result,
            s ← Statement.suff gs (Statement.True),
            pure $ Statement.By s r

meta def ApplyTree.mk_provided (rec : ApplyTree → tactic Statement): ApplyTree → tactic Statement
| a := do
      (gs, a) ← ApplyTree.collect_goals a,
      guard $ ¬gs.empty,
      rest ← rec a,
      cond ← Statement.for_some gs Statement.True,
      pure $ Statement.Provided (Statement.Have cond) rest

meta def ApplyTree.mk_results (rec : ApplyTree → tactic Statement) : ApplyTree → tactic Statement
| a := do
      (ss, a) ← ApplyTree.collect_srcs a,
      guard $ ¬ss.empty,
      cond ← Statement.ex (list.map source.value ss) Statement.True,

      rest ← rec a,
      pure $ Statement.meet [cond, rest]

meta def ApplyTree.toStatement : ApplyTree → tactic Statement
| a := (ApplyTree.mk_root a) <|> (ApplyTree.mk_provided ApplyTree.toStatement a) <|> (ApplyTree.mk_results ApplyTree.toStatement a)

meta def src_to_Statement : source → tactic Statement
| s := do
      f ← pure s.value,
      T ← infer_type f,
      Statement.ofProp T

meta def assert_with_reason : ReasonReduction → Statement → list Sentence
| (ReasonReduction.ShortReason r) s := [Sentence.ReasonedAssert r s]
| (ReasonReduction.Omit) s := [Sentence.BareAssert s]
| (ReasonReduction.Immediate) s := [Sentence.BareAssert s] -- [todo] difference with Omit?
| (ReasonReduction.LongReason ss) s := ss ++ [Sentence.Therefore $ Sentence.BareAssert s]

meta def ApplyTree.is_trivial : ApplyTree → bool
| (ApplyTree.Match _ _ []) := tt
| _ := ff

/--
- `Π xs Ps, ⋀ Qs, R` ⟿ "It suffices to find (cpc(xs, Ps)), since then we have R"
- `⋀ Qs, R` ⟿ "We have R"
- `∃ xs, ⋀ Qs, R` ⟿ "There exists (cpc(xs)) where Qs such that R"
- `∃ xs, Π ys Ps, R` ⟿ "There exists (cpc xs) such that it suffices to find ys such that R"
-/
meta def parse_Apply : list_parser tact tactic (list Sentence) := do
      ⟨targ, src, results⟩ ← ctest as_Apply,
      story ← pure src.story,
      rr ← ⍐ $ Reason.reduce story,
      results_reason ← ⍐ $ ApplyTree.get_source_reason results,
      -- ⍐ $ trace_m "parse_Apply: " $ (rr, results_reason),
      is_triv : bool ← pure $ band (ApplyTree.is_trivial results) $ band (rr.is_Omit) (Reason.is_Omit results_reason),
      if is_triv then pure [] else do
      -- if  then
      -- ⍐ $ trace_m "parse_Apply: " $ (rr),
      rr ← pure $ if rr.is_Immediate then ReasonReduction.ShortReason results_reason else rr,
      -- ⍐ $ trace_m "parse_Apply: " $ (rr),
      smt ← ⍐ $ ApplyTree.toStatement results,
      sentences ← pure $ assert_with_reason rr smt,
      -- ⍐ $ trace_m "parse_Apply: " $ (smt),
      -- [todo] adding reasons, sometimes a source lemma will not have been mentioned before and will have a 'story' attached to it.
      -- in this case a prior sentence should be added explaining the 'story'.
      pure $ sentences

meta def parse_Done : list_parser tact tactic (list Sentence) := do
      _ ← ctest as_ProofDone,
      pure $ singleton $ Sentence.WeAreDone

meta def parse_Tactic : list_parser tact tactic (list Sentence) := do
      (targ, label, results) ← ctest as_TargetTactic,
      smt ← monad_lift $ ApplyTree.toStatement results,
      pure $ singleton $ Sentence.BareAssert $ Statement.By smt (Reason.Tactic label)

meta def test_Scope : list_parser tact tactic (binder × tact) := do
      (ts, act.Scope n i) ← list_parser.take | failure,
      pure $ (n, (ts, i))

meta def get_case_name_from_binder : binder → tactic Statement
-- | ⟨`or.inl.CASE, _, y⟩ := do
--       -- tactic.trace_m "get_case_name_from_binder: " $ y,
--       (hh, _ )← returnopt $ expr.pi_binder y,
--       Statement.ofProp hh.type
| ⟨_, _, y⟩ := do
      (hh, _ )← returnopt $ expr.pi_binder y,
      Statement.ofProp hh.type

meta def parse_Scope (rec : list_parser tact tactic (list Sentence)) : list_parser tact tactic (list Sentence) := do
      (n, s0) ← test_Scope,
      ss ← many $ (do
            (m, s) ← test_Scope,
            guard $ m.name = n.name,
            pure s
      ),
      ss ← pure $ list.cons s0 ss,
      except.ok (sentences, []) ← ⍐ $ list_parser.run rec ss | failure,
      case_smt ← ⍐ $ get_case_name_from_binder n,
      pre ← pure $ Sentence.InCase case_smt,
      pure $ [ Sentence.LineBreak,  pre ] ++ sentences ++ [ Sentence.LineBreak ]

meta def parse_Cases : list_parser tact tactic (list Sentence) := do
      ss ← ctest as_Cases,
      ss ← ⍐ $ list.mmap Statement.ofProp $ list.map binder.type $ ss,
      pure $ [Sentence.BareAssert $ Statement.Have $ Statement.Either $ ss]

meta def parse_inputs : list_parser tact tactic (list Sentence) :=
list.join <$> many (
  parse_take
  <|> parse_choose
  <|> parse_Apply
  <|> parse_Done
  <|> parse_Tactic
  <|> parse_Scope parse_inputs
  <|> (ctest as_Andi *> pure [])
  <|> (parse_Cases)
  <|> (do
      x ← ctest some,
      xs ←  ⍐ $ pp x,
      pure $ singleton $ Sentence.BareAssert $ Statement.ofRun $ "don't know how to parse: " ++ xs.to_string
))

meta def inputs_to_sentences : list tact → tactic (list Sentence)
| cs := do
   xs ← list_parser.run (parse_inputs) cs,
   (xs, ys) ← tactic.return_except xs,
--    trace_m "inputs_to_sentences: " $ xs,
   pure xs

end writeup
end hp