import .run .data .table

/-!
Class predicate collections, as described in https://www.edayers.com/thesis/box#nlg-binders
-/

namespace hp.writeup

open hp.writeup.run

open tactic

meta def cp.contains_FoldAdj : list cp → bool
| l := option.is_some $ list.bfind cp.is_FoldAdjective l

section
variables {m : Type → Type} [monad m]
/-- Given the predicate `f`, partition the list in to two according to the presence of the predicate. -/
meta def cpc.partition_subjects (f : expr → m bool) : list cpc → m ((list cpc) × (list cpc))
| (⟨xs, ps⟩ :: rest) := do
  (i, o) ← list.mpartition f xs,
  (ins, outs) ← cpc.partition_subjects rest,
  ins ← pure $ if i.empty then ins else ⟨i,ps⟩::ins,
  outs ← pure $ if o.empty then outs else ⟨o,ps⟩::outs,
  pure $ (ins, outs)
| [] := pure ([],[])

end

/-- Takes a list of cpcs and puts them together to make a better flowing sentence.
The rules:
- x ▸ A, y ▸ A ↝ (x ++ y) ▸ A -- provided A doesn't contain a FoldAdjective
- x ▸ A, x ▸ B ↝ x ▸ (A ++ B)
There are other transformations that you could do, but these cover 80% of the cases.
I am also reluctant to do transformations that mix up the order.
 -/
meta def condense_pair : cpc → cpc → tactic (cpc)
| (c₁@⟨xs₁,cps₁⟩) (c₂@⟨xs₂, cps₂⟩) := do
  -- tactic.trace ("pair:", c₁, c₂),
  -- tactic.trace ("  ", expr.local_uniq_name <$> xs₁, expr.local_uniq_name <$> xs₂),
  xs_eq ← list.m_all (λ p : expr × expr, alternative.is_ok (tactic.is_def_eq p.1 p.2)) (list.zip xs₁ xs₂),
  if xs₁.length = xs₂.length ∧ xs_eq then do
    -- tactic.trace "same xs",
    match cps₁ with
    | [cp.SymbolicPostfix $ [run_item.Text ":", _]] := do
      -- tactic.trace "kill",
      pure ⟨xs₁, cps₂⟩
    | _ := pure ⟨xs₁, cps₁ ∪ cps₂⟩
    end
  else if (cps₁ = cps₂) ∧ ¬cp.contains_FoldAdj cps₁  then pure ⟨xs₁ ∪ xs₂, cps₁⟩ else
  failure

meta def condense_filter : cpc → bool
| ⟨[], _ ⟩ := ff
| ⟨_, []⟩ := ff
| _ := tt

meta def condense : list cpc → tactic (list cpc) | cpcs := do
  cpcs ← pure $ list.bfilter condense_filter cpcs,
  cpcs ← list.pair_rewrite condense_pair cpcs,
  pure cpcs

/-- This is used to create a cpc in the case that the given term's type is a
local constant. This happens eg with `x : G` ↝ "x is an element of G"-/
meta def cpc.of_local (t : writeup_table) (term : expr) : tactic cpc := do
  y ← infer_type term,
  -- [fixme] sadly, this fails for class instances that were intro'd
  cs ← tactic.get_classes y,
  ip ← is_prop y,
  -- find the first class in xs that has a entry in the writeup table.
  -- this will be used as an adjective to describe it.
  -- e.g., if `x : G` and `[group G]` then we get "let x be an element of G".
  r : cp ← @list.mfirst tactic _ _ _ _ (λ c, do
    match t.lct.get c with
    | (none) := failure
    | (some x) := pure (x y)
    end
  ) cs
  -- if there is no such class, a fallback is to just write "let x : G".
  -- unless the type `y` is a proposition.
  <|> ((guardb ¬ip) *> (pure $ cp.SymbolicPostfix $ Text ":" ++ Math y)),
  pure ⟨[term], [r]⟩


meta def cpc.type_symb (type val: expr) : cpc :=
⟨[val], [cp.SymbolicPostfix $ Text ":" ++ Math type]⟩

/-- Get the cpc for a given proposition -/
meta def cpc.of_prop (t : writeup_table) : expr → (tactic cpc)
| y := do
  ip ← is_prop y,
  guardb ip,
  xs ← pattern_table.get t.cpct y,
  dummy ← pure $ (expr.local_const `dummy `dummy binder_info.default y),
  xs ← pure $ xs.map ($ dummy),
  xs ← pure $ xs.filter (λ x, bnot $ assignable.has_local_constant dummy x),
  -- trace_m "cpc.of_prop: " $ xs,
  xs ← pure $ list.bfilter condense_filter xs,
  list.apick pure xs



meta def cpc.of_expr (t : writeup_table) : expr → (tactic cpc)
| e := do
  y ← infer_type e,
  match y with
  | (expr.local_const _ _ _ _) := cpc.of_local t e
  | (expr.sort level.zero) := pure ⟨[e], [cp.ClassNoun "proposition" "propositions"]⟩
  | (expr.sort _) := pure ⟨[e], []⟩
  | y := do
    xs ← pattern_table.get t.cpct y,
    ip ← is_prop y,
    xs ← if ip then pure xs else pure $ xs ++ [cpc.type_symb y],
    xs ← pure $ xs.map ($ e),
    cpc ← xs.mfirst pure,
    pure cpc
  end

/-- Converts a list of subject expressions to a list of cpcs and a list of 'remenant' expressions.
Usually the list of expressions are local constants that have just been introduced. -/
meta def to_cpcs (decls_only : bool) : list expr → tactic (list cpc × list expr)
| xs := do
  t ← get_writeup_table,
  -- ① an expression is a 'decl' if its a term or a sort. (ie, not a typeclass or a proof)
  -- these are the 'subjects'
  (subjects, others) ← xs.mpartition (λ x, pure bor <*> is_term x <*> pure (expr.is_sort x)),
  -- ② now convert each of the xs to a cpc.
  -- if it fails then it goes in a 'rest' list
  (cpcs, rest) ← xs.apartition (λ x, do
    cpc ← cpc.of_expr t x,
    -- only include cpcs that explicitly mention a subject.
    guardb $ ¬decls_only ∨ subjects.any (λ subject, contains_subject subject cpc),
    pure cpc
  ),
  cpcs ← condense cpcs,
  pure (cpcs, rest)

meta def to_cpc : expr → tactic cpc
| e := do
  t ← get_writeup_table,
  cpc.of_expr t e

/-- Tests if the given expression is contained as a subject of the given list of cpcs -/
meta def contains : expr → list cpc → bool
| x cpcs := list.any cpcs (λ ⟨xs,_⟩, x ∈ xs)

meta def is_plural : list cpc → bool
| [⟨[x], _⟩] := ff
| _ := tt

meta def first_mentions : (list cpc × list cpc) → list cpc → (list cpc × list cpc)
| ⟨c₁, c₂⟩ [] := ⟨list.reverse c₁, list.reverse c₂⟩
| ⟨c₁, c₂⟩ (⟨xs,ps⟩ :: t) :=
  match list.partition (λ x, contains x c₁) xs with
  | ([], ys) := first_mentions (⟨ys, ps⟩::c₁, c₂) t
  | (xs, []) := first_mentions (c₂, ⟨xs,ps⟩::c₂) t
  | (xs, ys) := first_mentions (⟨ys, ps⟩::c₁, ⟨xs,ps⟩::c₂) t
  end

inductive cpc_verb
| Is
| Be

def cpc_verb.plural : cpc_verb → string
| cpc_verb.Is := "are"
| cpc_verb.Be := "be"

def cpc_verb.singular : cpc_verb → string
| cpc_verb.Is := "is"
| cpc_verb.Be := "be"

meta def cpc.to_run (with_verb : option cpc_verb) (is_plural_default : bool) : cpc → option run
| c@⟨xs, ps⟩ := do
  is_plural : bool ← pure $ bor is_plural_default $ to_bool $ xs.length > 1,
  s ← pure $ cpc.to_string c,
  (sps, rest)   ← pure $ list.opartition cp.as_SymbolicPostfix ps,
  (adjs, rest)  ← pure $ list.opartition cp.as_Adjective rest,
  (fadjs, rest) ← pure $ list.opartition cp.as_FoldAdjective rest,
  (cns, [])   ← pure $ list.opartition cp.as_ClassNoun rest | none,
  -- (crs, [])     ← pure $ list.opartition cp.as_ClassRelational rest | none,
  -- if there is more than one classnoun or class relation things get tricky.
  if (cns.length > 1) then undefined_core "not implemented cpc.to_run multiple class nouns" else do -- implement by converting later classnouns to statements.
  adjs ← pure $ adjs ++ fadjs,
  noun ← pure $ (do
    base_noun ← list.ohead $ cns,
    base_noun ← pure $ if is_plural then prod.snd base_noun else prod.fst base_noun,
    adjs ← pure $ run.intercomma adjs,
    noun ← pure $ adjs ++ base_noun,
    pure noun
  ),
  -- trace ("cpc.to_run:" ++ s) (pure ()),
  sybs ← pure $ (run.intercomma $ list.map run.Math xs) ++ run.join sps,
  match noun, adjs, is_plural, with_verb with
  | none, [], _, _ := pure $ sybs
  | none, adjs, tt, (some v) := pure $ sybs ++ v.plural ++ andify adjs
  | none, adjs, ff, (some v) := pure $ sybs ++ v.singular ++ andify adjs
  | none, adjs, tt, none := pure $ sybs ++ "are" ++ andify adjs
  | none, adjs, ff, none := pure $ sybs ++ "is" ++ andify adjs
  | (some noun), _, tt, (some v) := pure $ sybs ++ v.plural ++ noun
  | (some noun), _, ff, (some v) := pure $ sybs ++ v.singular ++ "a" ++ noun -- eg "x:nat is a number", "let x:nat be a number"
  | (some noun), _, _ , none     := pure $ noun ++ sybs
  end

meta def cpcs.to_be_run : list cpc → run
| cs := "ERROR" <| run.andify <$> list.mmap (cpc.to_run (some cpc_verb.Be) ff) cs

meta def cpcs.to_is_run : list cpc → run
| cs := "ERROR" <| run.andify <$> list.mmap (cpc.to_run (some cpc_verb.Is) ff) cs

-- note that it's "for all numbers x" but "there exists a number x". It's always a plural for a pi.
meta def cpcs.to_quantifier_run (always_plural : bool) : list cpc → run
| cs := "ERROR" <| run.andify <$> list.mmap (cpc.to_run none always_plural) cs

meta def cpcs.to_verb_quantifier_run (singular plural : run) : list cpc → run
| cs@([⟨[x],_⟩]) := ((++) singular) $ cpcs.to_quantifier_run ff cs
| cs := ((++) plural) $ cpcs.to_quantifier_run ff cs

end hp.writeup
