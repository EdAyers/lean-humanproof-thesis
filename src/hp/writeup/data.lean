import .run hp.core

namespace hp.writeup

open hp

/-- Class predicate (CP). A class predicate is a predicate that can be used to declare a term.
So for example, you can say "Let `f : A → B` be a function" or "Let H be a normal subgroup of G" or "Let x, y and z be primes".
But you _can't_ write "Let `f` be injective on `A`", you have to write "Let `f` be a function which is injective on `A`"
  the parameter `A` means it doesn't work as an adjective: "Let `f` be an injective function on `A`".
There are currently 4 different kinds of CP:
- Adjective a predicate that should be treated as an adjective modifier.
  Examples are: "__open__ set", "__continuous__ function", "__normal__ subgroup".
- Fold Adjective is an adjective that applies to a collection of subjects.
  That is, it is a predicate of type `list subject → Prop`.
  Example: "__parallel__ lines".
- SymbolicPostfix are math-mode symbols that can be used to introduce a variable. For example `ε > 0`, `x y ∈ A`.
- ClassNoun are nouns that the given subject _is_. Eg "f is a __function__", "H is a __subgroup of G__".
-/
@[derive_prisms, derive decidable_eq, derive has_to_tactic_format]
meta inductive cp
| Adjective (r : run) -- adjectives must be strictly one word.
| FoldAdjective (r : run)
| SymbolicPostfix (e : run)
| ClassNoun (s p : run) -- "group"/"groups"
-- | ClassRelational (s p : run) (rhs : expr) -- "is/are subset[s] of" "element of" "function of". `s` and `p` come with `rhs` baked in but you need `rhs` for merging.
-- [todo] definite article tricks; "the least X such that Y"
-- [todo] ClassRelation packing; eg
  -- "(σ : ℕ → ℕ) (_ : ∀ n, prime (σ n))" ↝ "let σ be a sequence of prime numbers"
  -- "(X : set ℕ) (_ : ∀ x ∈ X, prime x)" ↝ "let X be a set of prime numbers"

/-- Class predicate collection. A list of class predicates to be rendered together.-/
@[derive_setters, derive decidable_eq, derive has_to_tactic_format]
meta structure cpc :=
(subjects : list expr)
(predicates : list cp)

/-- Class predicate collection __list__. -/
@[reducible]
meta def cpcs := list cpc

/-- An apply tree is a record of how an `apply` operation was performed.
Note that in HP, apply operations also unpack ∃ and ∧ propositions and automatically try discharging with `assumption`.

- Match the result was matched directly with the goal, with the given metavariables assigned
- ExistsElim value a: the applyer had the signature `∃ (x : X), P`
- AndElim value a : applyer had the signature `X ∧ Y` or `Y ∧ X`
- ApplyAssigned arg a; applyer had signature `Π (x : X), P` and `x` was assigned a value.
- ApplyGoal g a; applyer had signature `Π (x : X), P` but `x` was not assigned and hence appears as a new metavariable.
-/
@[derive_prisms, derive decidable_eq, derive has_to_tactic_format]
meta inductive ApplyTree : Type
| Match (result : expr) (goal : stub) (setters : list (stub × expr))
| ExistsElim (value : source) : ApplyTree -> ApplyTree
| AndElim (value : source) : ApplyTree -> ApplyTree
| ApplyAssigned (argument : expr) : ApplyTree -> ApplyTree
| ApplyGoal (name : name) (bi : binder_info) (stub : expr) : ApplyTree → ApplyTree

namespace ApplyTree

meta def getChild : ApplyTree → option ApplyTree
| (Match result goal setters) := none
| (ExistsElim value a) := some a
| (AndElim value a) := some a
| (ApplyAssigned argument a) := some a
| (ApplyGoal name bi stub a) := some a

meta def getAssigned : ApplyTree → list expr
| a := (id <| (some list.cons <*> (prod.fst <$> as_ApplyAssigned a))) $ ([] <| (getAssigned <$> getChild a))

meta def getGoals : ApplyTree → list expr
| a := (id <| (some list.cons <*> (as_ApplyGoal a >>= λ ⟨_,_,s,_⟩, some s))) $ ([] <| (getGoals <$> getChild a))

meta def getSources : ApplyTree → list source
| a := (id <| (some list.cons <*> ((as_ExistsElim a <|> as_AndElim a) >>= some ∘ prod.fst))) $ ([] <| (getSources <$> getChild a))

end ApplyTree

/-- A Statement corresponds to an intra-sentence proposition.
The proposition may be object-level or meta/context-level.

A Reason is some additional information that is used to justify statements.
-/
@[derive_prisms]
meta mutual inductive Reason, Statement

with Reason : Type
| BySetting (setters : list (stub × expr)) : Reason
-- "since A is open, "
| Since (smt : Statement) : Reason
| ofRun : run → Reason
-- "by applying norm_num, ", "by applying `ring`"...
| Tactic : string → Reason
-- don't include an explanation
| Omit

with Statement : Type
-- escape hatch for just writing out as string
| ofRun : run → Statement
| TermStatement (type : expr):  Statement
| CPC (cpc : cpc) : Statement
| Forall (binders : list cpc) (result : Statement) : Statement
| Exists (binders : list cpc) (result : Statement) : Statement
| Implies (premiss concl : Statement) : Statement
/-- Same as `Implies` but with ordering flipped. -/
| Whenever (premiss concl : Statement) : Statement
| And : list Statement → Statement
| By (s : Statement) (r : Reason) : Statement
/-- "`s` for some `...bs` where `where[bs]`". This is different to Exists because the 'binders' are already present in the context.
It's a meta-level statement about the tactic context rather than a standalone statement.
The 'where' are just other facts that might be relevant. -/
| ForSome (s : Statement) (binders : list cpc) (where : Statement) : Statement
-- it suffices to find `decls` such that `s`.
| Suffices (decls : list cpc) (s : Statement) : Statement
| Have (s : Statement)
| Provided (s1 s2 : Statement) : Statement
| Either (ss : list Statement) : Statement

section pp

open tactic Reason Statement format
meta mutual def Reason.pp, Statement.pp

with Reason.pp : Reason → tactic format
| (BySetting setters) := nest_join "BySetting" $ [pp setters]
| (Since smt) := nest_join "Since" $ [Statement.pp smt]
| (ofRun r) := nest_join "ofRun" $ [pp r]
| (Tactic t) := format.nest_join "Tactic" $ [pp t]
| (Omit) := format.nest_join "Omit" []

with Statement.pp : Statement → tactic format
| (ofRun r) := nest_join "ofRun" $ [pp r]
| (TermStatement t) := nest_join "TermStatement" [pp t]
| (CPC c) := nest_join "CPC" [pp c]
| (Either ss) := nest_join "Either" $ list.map Statement.pp ss
| _ := pure $ to_fmt "not implemented"

meta instance Statement.has_pp : has_to_tactic_format Statement := ⟨Statement.pp⟩
meta instance Reason.has_pp : has_to_tactic_format Reason := ⟨Reason.pp⟩

end pp

@[derive_prisms, derive has_to_tactic_format]
meta inductive Sentence -- [todo] merge with Statement?
/-- Introduce some variables and assumptions. -/
| Let (decls : list cpc) (where : Statement) : Sentence
/-- Restate the target. -/
| WeNeedToShow : Statement → Sentence
/-- Just print the statement. -/
| BareAssert : Statement → Sentence
| ReasonedAssert: Reason → Statement → Sentence
| WeAreDone
| Suffices (s : Statement) (r : Reason)
| Therefore : Sentence → Sentence
| WeMustChoose (decls : list cpc) : Statement → Sentence
/-- "In the case that ${s}: " -/
| InCase (s : Statement) : Sentence
| LineBreak : Sentence

-- | Since (s : Statement) (r : Reason) (result : Statement) : Sentence

/-- A high-level proof 'move'. The act type for the writeup procedure.
Given a stream of acts, one can produce a writeup.
[todo] rename to `act`. -/
@[derive_prisms, derive decidable_eq, derive has_to_tactic_format]
meta inductive act
| ProofDone
| Intro (h : list hyp)
| Existsi (v : stub) (prop : stub)
| Andi (l : stub) (r : stub)
| Apply (target : stub) (src : source) (results : ApplyTree)
| ExpandTarget
| TargetTactic (target : stub) (tactic_label : string) (results : ApplyTree)
/-- You can add a scope to an act to indicate that the microplanner should place it in its own paragraph.-/
| Scope : name → act → act
| Cases : list binder → act

open tactic

section

variables {m : Type → Type} [monad m] (f : telescope → expr → m expr)

meta def ApplyTree.mmap_exprs : telescope → ApplyTree → m ApplyTree
| Γ (ApplyTree.Match result goal setters) := pure ApplyTree.Match <*> assignable.mmap_children f Γ result <*> assignable.mmap_children f Γ goal <*> assignable.mmap_children f Γ setters
| Γ (ApplyTree.ExistsElim value a) := pure ApplyTree.ExistsElim <*> assignable.mmap_children f Γ value <*> ApplyTree.mmap_exprs Γ a
| Γ (ApplyTree.AndElim value a) := pure ApplyTree.AndElim <*> assignable.mmap_children f Γ value <*> ApplyTree.mmap_exprs Γ a
| Γ (ApplyTree.ApplyAssigned argument a) := pure ApplyTree.ApplyAssigned <*> assignable.mmap_children f Γ argument <*> ApplyTree.mmap_exprs Γ a
| Γ (ApplyTree.ApplyGoal name bi stub a) := pure ApplyTree.ApplyGoal <*> pure name <*> pure bi <*> assignable.mmap_children f Γ  stub <*> ApplyTree.mmap_exprs Γ a

meta def act.mmap_exprs : telescope → act → m act
| Γ act.ProofDone := pure act.ProofDone
| Γ (act.Intro a) := pure act.Intro <*> assignable.mmap_children f Γ a
| Γ (act.Existsi v prop) := pure act.Existsi <*> assignable.mmap_children f Γ v <*> assignable.mmap_children f Γ prop
| Γ (act.Andi a b) := pure act.Andi <*> assignable.mmap_children f Γ a <*> assignable.mmap_children f Γ b
| Γ (act.Apply target src results) := pure act.Apply <*> assignable.mmap_children f Γ target <*> assignable.mmap_children f Γ src <*> ApplyTree.mmap_exprs f Γ results
| Γ act.ExpandTarget := pure act.ExpandTarget
| Γ (act.TargetTactic target tactic_label results) := pure act.TargetTactic <*> assignable.mmap_children f Γ target <*> pure tactic_label <*> ApplyTree.mmap_exprs f Γ results
| Γ (act.Scope n i) := pure ( act.Scope n ) <*> act.mmap_exprs Γ i
| Γ (act.Cases s) := pure (act.Cases) <*> assignable.mmap_children f Γ s

end

meta instance act.assignable : assignable act := ⟨@act.mmap_exprs⟩
meta instance ApplyTree.assignable : assignable ApplyTree := ⟨@ApplyTree.mmap_exprs⟩

meta def cp.pp : cp → tactic format
| (cp.Adjective r)       := (format.compose "Adjective ")       <$> tactic.pp r
| (cp.FoldAdjective r)   := (format.compose "FoldAdjective ")   <$> tactic.pp r
| (cp.SymbolicPostfix e) := (format.compose "SymbolicPostfix ") <$> tactic.pp e
| (cp.ClassNoun s p)     := pure (λ s p, "ClassNoun " ++ s ++ " " ++ p) <*> tactic.pp s <*> tactic.pp p
-- | (cp.ClassRelational s p rhs) :=  pure (λ s p r, "ClassRelational " ++ s ++ " " ++ p ++ " " ++ r) <*> tactic.pp s <*> tactic.pp p <*> tactic.pp rhs

meta def cp.to_string : cp → string
| (cp.Adjective r)       := ("Adjective ")       ++ to_string r
| (cp.FoldAdjective r)   := ("FoldAdjective ")   ++ to_string r
| (cp.SymbolicPostfix e) := ("SymbolicPostfix ") ++ to_string e
| (cp.ClassNoun s p)     := "ClassNoun " ++ to_string s ++ " " ++ to_string p
-- | (cp.ClassRelational s p rhs) :=  "ClassRelational " ++ to_string s ++ " " ++ to_string p ++ " " ++ to_string rhs

meta instance cp.has_pp : has_to_tactic_format cp := ⟨cp.pp⟩
meta instance cp.has_to_string : has_to_string cp := ⟨cp.to_string⟩

meta def cpc.to_string : cpc → string
| ⟨ss, ps⟩ := "⟨" ++ to_string ss ++ ", " ++ to_string ps ++ "⟩"

meta def cpc.pp : cpc → tactic format
| ⟨ss, ps⟩ := do
  ss ← tactic.pp ss,
  ps ← tactic.pp ps,
  pure $ "⟨" ++ ss ++ ", " ++ ps ++ "⟩"

meta instance cpc.has_pp : has_to_tactic_format cpc := ⟨cpc.pp⟩

meta instance cpc.has_to_string : has_to_string cpc := ⟨cpc.to_string⟩

meta def contains_subject : expr → cpc → bool
| e ⟨xs, _⟩ := e ∈ xs

section
variables {m : Type → Type} [monad m]
meta def cp.mmap_exprs  (f : telescope → expr → m expr) : telescope → cp → m cp
| Γ (cp.Adjective r) := (pure cp.Adjective) <*> ((Γ ⍄ f) r)
| Γ (cp.FoldAdjective r) := (pure cp.FoldAdjective) <*> ((Γ ⍄ f) r)
| Γ (cp.SymbolicPostfix r) := (pure cp.SymbolicPostfix) <*> ((Γ ⍄ f) r)
| Γ (cp.ClassNoun s p) := pure (cp.ClassNoun s p)

meta instance cp.has_assignable : assignable cp := ⟨@cp.mmap_exprs⟩

meta def cpc.mmap_exprs (f : telescope → expr → m expr) : telescope → cpc → m cpc
| Γ ⟨subjects, cps⟩ := (pure cpc.mk) <*> (list.mmap (f Γ) subjects) <*> (list.mmap (Γ ⍄ f) cps)

meta instance cpc.has_assignable : assignable cpc := ⟨@cpc.mmap_exprs⟩

-- meta def cpc.cpcs_assignable : assignable cpcs := by apply_instance

end
end hp.writeup