/- Author: E.W.Ayers © 2019 -/
import .submatch
open tactic expr
namespace hp

@[derive_prisms]
meta structure rule_table :=
(head_table : prerule_table)
(submatch_table : submatch_table)

namespace rule_table

meta def empty : rule_table := {head_table := ∅, submatch_table := ∅}

meta instance : has_emptyc rule_table := ⟨empty⟩

meta def insert : name → rule_table → tactic rule_table
| n old := do
    prs ← prerule.of_name n,
    head_table ← pure $ prs.foldr prerule_table.insert old.head_table,
    submatch_table ← prs.mfoldl submatch_table.insert old.submatch_table,
    pure {head_table := head_table, submatch_table := submatch_table}

/-- Take each rule in r₁ and insert to r₂. -/
meta def union (r₁ r₂ : rule_table) : rule_table :=
    { head_table     := r₁.head_table     ∪ r₂.head_table
    , submatch_table := r₁.submatch_table ∪ r₂.submatch_table }

meta instance : has_union rule_table := ⟨union⟩

meta def list_union (l : list rule_table) : rule_table := list.foldl (∪) ∅ l

/-- Entry point for buiding a rule table from a set of declarations. -/
meta def of_names (ns : list name) : tactic rule_table := do
    ns.mfoldr insert ∅
    -- rs ← ns.mmap rule.of_name,
    -- revs ← list.mchoose (λ r, do ic ← rule.is_commuter r, if ic then failure else rule.flip r) rs,
    -- of_rules $ rs ++ revs
private meta def get_head_rewrites : name → rule_table → table prerule | k {head_table := ht, ..} := ht.get k

meta structure rewrites_config :=
(wilds := ff)

/- setting wilds causes inclusion of rules such as `?x = ?x * 1` where the lhs can be anything.
    This slows things down substantially
    [TODO] these 'wild' rules are handled by their own system.
    [TODO] optimise so that there are some type/typeclass checks on it.
    (annihilators := ff) [TODO] -/


-- meta def head_rewrites_rhs (rhs : expr) (rt : rule_table) (cfg : rewrites_config := {}) : (tactic $ list rule) := do
--     head_rewrites rhs rt >>= list.mmap rule.flip

/-- Finds the _equality_ submatches for a given expression. -/
meta def submatch : rule_table → expr → tactic (list (address × rule))
| rt e := do
    sms ← rt.submatch_table.run e,
    sms.mmap (λ ⟨a,r⟩, do
        p ← returnopt $ expr.zipper.to_path a e,
        r ← rule.congr p r,
        pure ⟨a,r⟩
    )

meta instance : has_to_tactic_format rule_table := ⟨tactic.pp ∘ head_table⟩

meta def raw_rewrites : rule_table → expr → tactic (list (rule × zipper.path))
| rt e := rt.head_table.rewrites e

meta def rewrites : rule_table → expr → tactic (list rule)
| rt e := raw_rewrites rt e >>= list.mmap (function.uncurry rule.congr ∘ prod.swap)

end rule_table
end hp