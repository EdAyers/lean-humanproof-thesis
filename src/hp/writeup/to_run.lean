import .writeup hp.core

namespace hp.writeup
open run
meta mutual def Reason.to_run, Statement.to_run

with Reason.to_run : Reason →  run
| (Reason.BySetting setters) :=
  run.append ("by setting")
  $ andify
  $ setters.map (λ ⟨s,a⟩, s.pretty_name ++ "to be" ++ run.Math a)
| (Reason.Since s) := run.append "since" $ Statement.to_run s
| (Reason.ofRun r) := r
-- | (Reason.HAve)
| Reason.Omit := ""
| (Reason.Tactic l) := "by" ++ l

with Statement.to_run : Statement → run
| (Statement.ofRun r) := r
| (Statement.TermStatement t) := run.Math t
| (Statement.CPC xs) := "error in Statement.to_run" <| cpc.to_run (some cpc_verb.Is) ff xs
| (Statement.Forall [] r) := Statement.to_run r
| (Statement.Forall bs s@(Statement.Exists cs r)) := "for all" ++ cpcs.to_quantifier_run tt bs ++ "," ++ Statement.to_run s
| (Statement.Forall bs r) := Statement.to_run r ++ "for all" ++ cpcs.to_quantifier_run tt bs
| (Statement.Exists [] r) := Statement.to_run r
| (Statement.Exists bs (Statement.And [])) := cpcs.to_verb_quantifier_run ("there exists" ++ "a") "there exists" bs
| (Statement.Exists bs r) := cpcs.to_verb_quantifier_run ("there exists" ++ "a") "there exists" bs ++ "such that" ++ Statement.to_run r
| (Statement.Implies p c) := Statement.to_run p ++ "implies" ++ Statement.to_run c
| (Statement.Whenever p c) := Statement.to_run c ++ "whenever" ++ Statement.to_run p
| (Statement.And ss) := andify $ Statement.to_run <$> ss
| (Statement.By s (Reason.Omit)) := Statement.to_run s
| (Statement.By s r) := Statement.to_run s ++ "," ++ Reason.to_run r
| (Statement.ForSome concl decls where) :=
  let w : run := if Statement.is_True where then "" else "where" ++ where.to_run in
  concl.to_run ++ "for some" ++ cpcs.to_quantifier_run ff decls ++ w
| (Statement.Suffices [] x) := "it suffices to show" ++ Statement.to_run x
| (Statement.Suffices bs x) :=
  let st : run := if Statement.is_True x then "" else "such that" ++ Statement.to_run x in
  let article : run := if is_plural bs then "" else "a" in
  "it suffices to find" ++ article ++ (cpcs.to_quantifier_run ff bs) ++ st
| (Statement.Provided x y) := "provided" ++ x.to_run ++ "," ++ y.to_run
| (Statement.Have s) := "we have" ++ s.to_run
| (Statement.Either ss) := (run.append "either ") $ orify $ list.map Statement.to_run $ ss
open Sentence Statement

meta def Sentence.to_run_core : Sentence → run
| (WeNeedToShow s) := "we need to show that" ++ s.to_run
| (WeMustChoose ds s) :=
  let article : run := if is_plural ds then "" else "a" in
  "we must choose" ++ article ++ cpcs.to_quantifier_run ff ds ++ "such that" ++ s.to_run
| (BareAssert s) := (s.to_run)
| (WeAreDone) := "we are done"
| (Suffices s r) := (Reason.to_run r) ++ ", it suffices to show" ++ s.to_run
-- | (Have s r) := "We have " ++ s.to_run ++ r.to_run
| (Therefore s) := "so" ++ s.to_run_core -- [todo] this should be 'but' when the last thing we talked about was a 'suffices to show'
-- | (Since s r res) := "Since" ++ s.to_run ++ "," ++ r.to_run ++ "we have" ++ res.to_run
| (Let [] where) := (if where.is_True then "" else "assume" ++ where.to_run) -- [todo] assume should distribute over anded statements.
| (Let decls where) := "let" ++ cpcs.to_be_run decls ++ (if where.is_True then "" else "where" ++ where.to_run)
| (LineBreak) := "\n"
| (InCase smt) :=
  "in the case " ++ smt.to_run ++ ":"

meta def Sentence.to_run : Sentence → run
| s := run.capitalise (Sentence.to_run_core s) ++ "."

open widget

meta def write (dont_instantiate : list (expr × name)) : list tact → tactic (html empty)
| cs := do
  ss ← inputs_to_sentences cs,
  -- tactic.trace ss,
  r ← pure $ run.join $ Sentence.to_run <$> ss,
  r ← list.mfoldr hp.dummify r dont_instantiate,
  tactic.trace r,
  x ← run.view r,
  -- x : html empty ← pure $ [run.to_string r],
  pure $ h "div" [] x

end hp.writeup