/- This file contains lookup tables for words etc in the writeup.
The eventual goal is to replace this table with a set of attributes but this is how it works for now.
-/
import .data data.real.basic

namespace hp.writeup

meta def prop_patterns : tactic (pattern_table Statement) := do -- [todo] make this an attribute, or at
      ps ← list.mmap id [
            pattern_table.entry.of_pexpr ```(λ α β (f : α → β) (A : set α), @set.inj_on α β f A) (λ es, do [α, β, f, A] ← pure es, pure $ Statement.ofRun $ (run.Math f ++ run.Text "is injective on" ++ run.Math A) )
      ],
      pure $ pattern_table.of_list ps

meta structure writeup_table :=
(cpct : pattern_table (expr → cpc))
(lct : dict name (expr → cp)) -- eg `subgroup ↦ λ x,  "element of " ++ x.type` -- [todo] category morphism
(pt : pattern_table Statement)

meta def cp.simple_RelationalNoun (s : string) (preposition : run) (rhs : expr) :=
cp.ClassNoun (run.Text s ++ preposition ++ run.Math rhs) ((run.Text $ s ++ "s") ++ preposition ++ run.Math rhs)

meta def default_cpct : list (tactic (pattern_table.entry (expr → cpc))):= [
  pattern_table.entry.of_pexpr ```(λ α, group α)  (λ es, do [α] ← pure es, pure $ λ _, cpc.mk [α] $ [cp.ClassNoun "group" "groups"]),
  pattern_table.entry.of_pexpr ```(λ α, metric_space α)  (λ es, do [α] ← pure es, pure $ λ _, cpc.mk [α] $ [cp.ClassNoun "metric space" "metric spaces"]),
  pattern_table.entry.of_pexpr ```(λ α, met_space α)  (λ es, do [α] ← pure es, pure $ λ _, cpc.mk [α] $ [cp.ClassNoun "metric space" "metric spaces"]),
  pattern_table.entry.of_pexpr ```(λ α, monoid α) (λ es, do [α] ← pure es, pure $ λ _, cpc.mk [α] $ [cp.ClassNoun "monoid" "monoids"]),
  pattern_table.entry.of_pexpr ```(λ α [g : group α], @subgroup α g) (λ es, do [α] ← pure es, pure $ λ x, cpc.mk [x] $ [cp.simple_RelationalNoun "subgroup" "of" α]),
  pattern_table.entry.of_pexpr ```(λ α [g : group α] H, @subgroup.normal α g H) (λ es, do [α] ← pure es, pure $ λ x, cpc.mk [α] $ [cp.Adjective "normal"]),

  pattern_table.entry.of_pexpr ```(λ α, list α)   (λ es, do [α] ← pure es, pure $ λ x, cpc.mk [x] $ [cp.simple_RelationalNoun "list" "of" α]),
  pattern_table.entry.of_pexpr ```(λ α, set α)    (λ es, do [α] ← pure es, pure $ λ x, cpc.mk [x] $ [cp.simple_RelationalNoun "set" "on" α]),
  pattern_table.entry.of_pexpr ```(nat) (λ _, pure $ λ e, cpc.mk [e] [cp.ClassNoun "natural number" "natural numbers"]),
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
dict.insert `semigroup (cp.simple_RelationalNoun "element" "of") $ ∅

meta def default_writeup_table : tactic writeup_table := do
  cpctt ← list.achoose id default_cpct, -- [todo] in production make this mcollect.
  cpct ← pure $ pattern_table.of_list cpctt,
  lct ← pure $ default_lct,
  ppt ← prop_patterns,
  pure ⟨cpct, lct, ppt⟩

meta def writeup_table.of_names : list name → tactic (writeup_table)
| ns := -- [todo]
  default_writeup_table

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

meta def writeup_attr : user_attribute writeup_table unit :=
{ name := `writeup
, descr := "tbd"
, cache_cfg :=
  { mk_cache := writeup_table.of_names
  , dependencies := []
  }
}

run_cmd attribute.register `hp.writeup.writeup_attr

meta def get_writeup_table : tactic writeup_table := user_attribute.get_cache writeup_attr

meta def get_prop_writeup : expr → tactic Statement | P  := do
  wt ← get_writeup_table,
  as ← wt.pt.get P,
  -- tactic.trace "get_prop_writeup",
  -- tactic.trace wt.pt,
  -- tactic.trace $ Statement.to_string <$> as,
  list.apick pure as

end hp.writeup