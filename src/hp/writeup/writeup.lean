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

/-- ⋀ a load of statements -/
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
      | P := (get_prop_writeup P) <|> (pure $ Statement.TermStatement P)
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

meta inductive ReasonReduction
| LongReason : list Sentence → ReasonReduction
| ShortReason : Reason → ReasonReduction
| Immediate : ReasonReduction
| Omit

open Reason ReasonReduction

meta def Reason.reduce : SourceReason → ReasonReduction
| (SourceReason.Assumption h) := Immediate
| (SourceReason.Since r) := Immediate
| (SourceReason.Forward implication premiss) := undefined_core "not implemented Reason.reduce"
| (SourceReason.And r1 r2) := undefined_core "not implemented Reason.reduce"
| (SourceReason.ConjElim conj index) := undefined_core "not implemented Reason.reduce"
| SourceReason.Omit := Omit
| (SourceReason.ExpandLocal r src) := undefined_core "not implemented Reason.reduce"
| (SourceReason.Setting r setters) :=
      ShortReason $ Reason.BySetting $ setters

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
  new_vars ← ⍐ $ list.mfilter (λ x, pure bor <*> is_term x <*> is_type x) $ takes.map hyp.to_expr,
  (cpcs, other_hyps) ← ⍐ $ to_cpcs ff $ list.map hyp.to_expr $ takes,
--   monad_lift $ tactic.trace "~~~ parse_take ~~~ ",
--   monad_lift $ tactic.trace $ cpcs,
  (new_var_cpcs, cpcs) ← cpc.partition_subjects (λ x, pure $ x ∈ new_vars) cpcs,
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

meta def ApplyTree.collect_srcs : ApplyTree → tactic (list source × ApplyTree)
| (ApplyTree.AndElim s a) := do ⟨gs, a⟩ ← ApplyTree.collect_srcs a, pure $ (s::gs, a)
| (ApplyTree.ExistsElim s a) := do ⟨gs, a⟩ ← ApplyTree.collect_srcs a, pure $ (s::gs, a)
| (ApplyTree.ApplyAssigned _ a) := ApplyTree.collect_srcs a
| a := pure ([],a)

meta def ApplyTree.mk_root : ApplyTree → tactic Statement
| a := do
      (gs, ApplyTree.Match result goal setters) ← ApplyTree.collect_goals a,
      if gs.empty then do
            gt ← pure $ goal.type,
            s ← Statement.ofProp gt,
            r ← pure $ if setters.empty then Reason.Omit else Reason.BySetting setters,
            pure $ Statement.By (Statement.Have s) r
      else do
            gt ← pure $ goal.type,
            r ← pure $ if setters.empty then Reason.Omit else Reason.BySetting setters,
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
      y ← infer_type s.value, -- [todo] what if it's not a prop?
      Statement.ofProp y

/--
- `Π xs Ps, ⋀ Qs, R` ⟿ "It suffices to find (cpc(xs, Ps)), since then we have R"
- `⋀ Qs, R` ⟿ "We have R"
- `∃ xs, ⋀ Qs, R` ⟿ "There exists (cpc(xs)) where Qs such that R"
- `∃ xs, Π ys Ps, R` ⟿ "There exists (cpc xs) such that it suffices to find ys such that R"
[todo] improve this code to match up with Mohan's version.
-/
meta def parse_Apply : list_parser tact tactic (list Sentence) := do
      ⟨targ, src, results⟩ ← ctest as_Apply,
      smt ← monad_lift $ ApplyTree.toStatement results,
      -- [todo] anaphor, use hence or therefore if the lemma src or applyAssigns are in context or were talked about recently.
      -- for now we just always use 'therefore'
      -- [todo] adding reasons, sometimes a source lemma will not have been mentioned before and will have a 'story' attached to it.
      -- in this case a prior sentence should be added explaining the 'story'.
      pure $ singleton $ Sentence.Therefore $ Sentence.BareAssert smt

meta def parse_Done : list_parser tact tactic (list Sentence) := do
      _ ← ctest as_ProofDone,
      pure $ singleton $ Sentence.WeAreDone

meta def parse_Tactic : list_parser tact tactic (list Sentence) := do
      (targ, label, results) ← ctest as_TargetTactic,
      smt ← monad_lift $ ApplyTree.toStatement results,
      pure $ singleton $ Sentence.BareAssert $ Statement.By smt (Reason.Tactic label)

meta def test_Scope : list_parser tact tactic (name × tact) := do
      (ts, act.Scope n i) ← list_parser.take | failure,
      pure $ (n, (ts, i))

meta def parse_Scope (rec : list_parser tact tactic (list Sentence)) : list_parser tact tactic (list Sentence) := do
      (n, s0) ← test_Scope,
      ss ← many $ (do
            (m, s) ← test_Scope,
            guard $ m = n,
            pure s
      ),
      ss ← pure $ list.cons s0 ss,
      except.ok (sentences, []) ← ⍐ $ list_parser.run rec ss | failure,
      pre ← pure $ Sentence.InCase (Statement.ofRun "case goes here"),
      post ← pure $ Sentence.LineBreak,
      pure $ [ pre ] ++ sentences ++ [ post ]

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
   (xs, ys) ← return_except xs,
   pure xs

end writeup
end hp