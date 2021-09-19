import .data data.real.basic
import group_theory.subgroup
/-!
This file contains the default class-predicate-collections for the humanproof writeup.

[todo] Use attributes instead of a hard-coded table for class predicates.

-/

namespace hp.writeup

meta def prop_patterns : tactic (pattern_table Statement) := do
      ps ← list.mmap id [
            pattern_table.entry.of_pexpr ```(λ α β (f : α → β) (A : set α), @set.inj_on α β f A) (λ es, do [α, β, f, A] ← pure es, pure $ Statement.ofRun $ (run.Math f ++ run.Text "is injective on" ++ run.Math A) )
      ],
      pure $ pattern_table.of_list ps

meta structure writeup_table :=
(cpct : pattern_table (expr → cpc))
(lct : dict name (expr → cp)) -- eg `subgroup ↦ λ x,  "element of " ++ x.type` -- [todo] category morphism
(pt : pattern_table Statement)

namespace writeup_table

  meta def join : writeup_table → writeup_table → writeup_table
  | ⟨c₁,l₁,p₁⟩ ⟨c₂, l₂, p₂⟩ := ⟨c₁ ++ c₂, dict.merge l₁ l₂, p₁ ++ p₂⟩

  meta instance : has_union writeup_table := ⟨join⟩

  meta def of_cpct : pattern_table (expr → cpc) → writeup_table
  | cpct := {cpct := cpct, lct := ∅, pt := ∅}

end writeup_table

meta def cp.relational_noun (singular : string) (plural : option string) (preposition : run) (rhs : expr) :=
  let plural := (singular ++ "s") <| plural in
  cp.ClassNoun
    (run.Text singular ++ preposition ++ run.Math rhs)
    (run.Text plural   ++ preposition ++ run.Math rhs)

meta def mk_adjective (n : name) (text : option string) : tactic (pattern_table.entry (expr → cpc)) := do
  f ← tactic.mk_const n,
  y ← tactic.infer_type f,
  (ps, b) ← pure $ telescope.of_pis y,
  guard (ps.length > 0),
  subject_index ← telescope.find_index (λ b, b.is_explicit) ps,
  pattern ← pure $ to_pexpr $ telescope.reverse_beta ps f,
  text ← pure $ n.to_string <| text,
  pattern_table.entry.of_pexpr pattern $ λ es, do subject ← es.nth subject_index, pure $ λ _, cpc.mk [subject] $ [cp.Adjective n.to_string]

meta def mk_classnoun (n : name) (singular plural : option string) : tactic (pattern_table.entry (expr → cpc)) := do
  f ← tactic.mk_const n,
  singular ← pure $ n.to_string <| singular,
  plural ← pure $ (singular ++ "s") <| plural,
  y ← tactic.infer_type f,
  (ps, b) ← pure $ telescope.of_pis y,
  guard (ps.length > 0),
  subject_index ← telescope.find_index (λ b, b.is_explicit) ps,
  pattern ← pure $ to_pexpr $ telescope.reverse_beta ps f,
  pattern_table.entry.of_pexpr pattern $ λ es, do subject ← es.nth subject_index, pure $ λ _, cpc.mk [subject] $ [cp.ClassNoun singular plural]

meta def mk_noun (n : name) (singular plural : option string) : tactic (pattern_table.entry (expr → cpc)):= do
  f ← tactic.mk_const n,
  singular ← pure $ n.to_string <| singular,
  plural ← pure $ (singular ++ "s") <| plural,
  y ← tactic.infer_type f,
  (ps, b) ← pure $ telescope.of_pis y,
  guard (ps.length > 0),
  pattern ← pure $ to_pexpr $ telescope.reverse_beta ps f,
  pattern_table.entry.of_pexpr pattern $ λ es, do pure $ λ x, cpc.mk [x] $ [cp.ClassNoun singular plural]

meta def mk_relational_noun (n : name) (singular plural : option string) (preposition : string) : tactic (pattern_table.entry (expr → cpc)) := do
  f ← tactic.mk_const n,
  singular ← pure $ n.to_string <| singular,
  plural ← pure $ (singular ++ "s") <| plural,
  y ← tactic.infer_type f,
  (ps, b) ← pure $ telescope.of_pis y,
  guard (ps.length > 0),
  object_index ← telescope.find_index (λ b, b.is_explicit) ps,
  pattern ← pure $ to_pexpr $ telescope.reverse_beta ps f,
  pattern_table.entry.of_pexpr pattern $ λ es, do object ← es.nth object_index, pure $ λ subject, cpc.mk [subject] $ [cp.relational_noun singular plural preposition object]

meta def default_cpct : list (tactic (pattern_table.entry (expr → cpc))):= [
  -- mk_classnoun `group none none,
  -- mk_classnoun `metric_space (some "metric space") none,
  -- mk_classnoun `met_space (some "metric space") none,
  -- mk_classnoun `monoid none none,
  mk_relational_noun `subgroup none none "of",
  -- pattern_table.entry.of_pexpr ```(λ α [g : group α], @subgroup α g) (λ es, do [α] ← pure es, pure $ λ x, cpc.mk [x] $ [cp.simple_RelationalNoun "subgroup" "of" α]),
  mk_adjective `subgroup.normal (some "normal"),
  -- pattern_table.entry.of_pexpr ```(λ α [g : group α] H, @subgroup.normal α g H) (λ es, do [α, g, H] ← pure es, pure $ λ x, cpc.mk [H] $ [cp.Adjective "normal"]),

  mk_relational_noun `list none none "of",
  -- pattern_table.entry.of_pexpr ```(λ α, list α)   (λ es, do [α] ← pure es, pure $ λ x, cpc.mk [x] $ [cp.simple_RelationalNoun "list" "of" α]),
  mk_relational_noun `set none none "of",
  -- pattern_table.entry.of_pexpr ```(λ α, set α)    (λ es, do [α] ← pure es, pure $ λ x, cpc.mk [x] $ [cp.simple_RelationalNoun "set" "on" α]),
  mk_noun `nat (some "natural number") none,
  -- pattern_table.entry.of_pexpr ```(nat) (λ _, pure $ λ e, cpc.mk [e] [cp.ClassNoun "natural number" "natural numbers"]),
  -- pattern_table.entry.of_pexpr ```(λ (α) (x : α) (X : set α), X x) (λ es, do
  --   [α,x,X] ← pure es,
  --   r : run ← pure $ (run.Text "∈") ++ run.Math X, -- [todo] need a way of printing '∈ X' as an expression.
  --   pure $ λ _, cpc.mk [x] $ [cp.SymbolicPostfix $ r]),
  pattern_table.entry.of_pexpr ```(λ (α β) (x : α) (X : β) (hm: has_mem α β), @has_mem.mem α β hm x X) (λ es, do
    [α,β,x,X,hm] ← pure es,
    r : run ← pure $ (run.Text "∈") ++ run.Math X, -- [todo] need a way of printing '∈ X' as an expression.
    pure $ λ _, cpc.mk [x] $ [cp.SymbolicPostfix $ r]),

  pattern_table.entry.of_pexpr ```(λ (x : ℝ), x > (0 : ℝ)) (λ es, do
    -- tactic.trace "hello this matched",
    [x] ← pure es,
    r : run ← pure $ (run.Text ">") ++ run.Math `(0 : ℝ),
    pure $ λ _, cpc.mk [x] $ [cp.SymbolicPostfix $ r]),
  -- pattern_table.entry.of_pexpr ```(λ α [m : metric_space α] (X : set α), @is_open α m X) (λ es, do [α,ms,  X] ← pure es, pure $ λ x, cpc.mk [X] $ [cp.Adjective "open"]),
  pattern_table.entry.of_pexpr ```(λ α [m : met_space α] (X : set α), @examples.is_open α m X) (λ es, do [α,ms,  X] ← pure es, pure $ λ x, cpc.mk [X] $ [cp.Adjective "open"])
]

meta def default_lct : dict name (expr → cp) :=
dict.insert `semigroup (cp.relational_noun "element" none "of") $ ∅

meta def default_writeup_table : tactic writeup_table := do
  cpctt ← list.achoose id default_cpct, -- [todo] in production make this mcollect.
  cpct ← pure $ pattern_table.of_list cpctt,
  lct ← pure $ default_lct,
  ppt ← prop_patterns,
  pure ⟨cpct, lct, ppt⟩

-- meta def adjectives_from_names : list name → tactic (writeup_table)
-- | ns :=


/- [todo]:
  user should be able to specify their own natural langauge translatoins without having to
  edit the above tables. However I need to think about the cleanest way to do this so that the
  user attributes don't look bad.

  eg something like:
  ```
  @[writeup (f is "injective on" A)]
  def set.inj_on f A : Prop := ...
  ```

  Note that `is` is a special verb object that changes the conjugation
  based on where the statement appears or how many 'f's the system is talking about.
-/


open lean.parser

meta def word : lean.parser string := lean.parser.pexpr >>= λ p, of_tactic $ tactic.eval_pexpr string $ p
@[user_attribute]
meta def writeup_classnoun_attr : user_attribute writeup_table (option string × option string) :=
{ name := `classnoun
, descr := "This will be written as an classnoun in natural language writeups."
, parser := ((pure prod.mk) <*> (optional word) <*> (optional word))
, cache_cfg :=
  { mk_cache := (λ ns, do
    ps ← ns.mmap (λ n, do
      (s,p) ← user_attribute.get_param writeup_classnoun_attr n,
      mk_classnoun n s p
    ),
    pure $ writeup_table.mk (pattern_table.of_list ps) ∅ ∅)
  , dependencies := []
  }
}

attribute [classnoun "group" "groups"] group
attribute [classnoun "monoid" "monoids"] monoid

meta def get_writeup_table : tactic writeup_table := do
  wt ← default_writeup_table,
  cwt ← user_attribute.get_cache writeup_classnoun_attr,
  pure $ wt ∪ cwt
  -- [todo] optimise by using 'dependencies' of attributes and daisy-chaining together the writeuptable.

meta def get_prop_writeup : expr → tactic Statement | P  := do
  wt ← get_writeup_table,
  as ← wt.pt.get P,
  -- tactic.trace "get_prop_writeup",
  -- tactic.trace wt.pt,
  -- tactic.trace $ Statement.to_string <$> as,
  list.apick pure as

end hp.writeup