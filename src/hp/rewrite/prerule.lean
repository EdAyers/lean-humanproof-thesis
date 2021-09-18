import .rule hp.core

open tactic expr

namespace hp

/-- A rule can't have higher-order parameters. A pre-rule can. -/
meta structure prerule :=
(pf : name)
(ctxt : telescope)
(body : expr) -- ctxt ⊢
(key : name)
(pp : format)
(reverse := ff)

namespace prerule
    meta instance prpp : has_to_tactic_format prerule := ⟨λ pr, do
        n ← tactic.pp pr.pf,
        t ← pure $ pr.pp,
        pure $ n ++ " : " ++ t⟩
    meta instance has_lt : has_lt prerule := ⟨λ x y, (x.reverse, x.pf) < (y.reverse, y.pf)⟩
    meta instance dec_lt : decidable_rel ((<) : prerule → prerule → Prop) := by apply_instance
    meta def lhs_rhs : prerule → tactic (expr × expr) | pr := do
        (_,l,r) ← tactic.relation_lhs_rhs pr.body,
        pure $ if pr.reverse then (r,l) else (l,r)
    meta def is_commuter : prerule → tactic bool | pr := do
        (r,lhs,rhs) ← tactic.relation_lhs_rhs pr.body,
        pure $ option.is_some $ expr.is_commute_raw lhs rhs
    meta def of_name : name → tactic (list prerule) | n := do
        pf   ← resolve_name n >>= pure ∘ pexpr.mk_explicit >>= to_expr,
        T    ← infer_type pf,
        (ctxt, body) ← pure $ telescope.of_pis T,
        (rel_name, lhs, rhs) ← tactic.relation_lhs_rhs body,
        lkey ← pure $ expr_table.get_key lhs,
        rkey ← pure $ expr_table.get_key rhs,
        text ← tactic.pp T,
        fwd  ← pure $ prerule.mk n ctxt body lkey (text) ff,
        bwd  ← pure $ prerule.mk n ctxt body rkey ("←" ++ text) tt,
        ic   ← pure $ option.is_some $ expr.is_commute_raw lhs rhs,
        prs  ← pure $ if ic then [fwd] else [fwd, bwd],
        pure prs
    meta def get_key : prerule → name | pr := pr.key
    meta def convert : expr → prerule → tactic rule | e pr := do
        ms ← pr.ctxt.to_metas,
        body ← pure $ expr.instantiate_vars pr.body ms,
        (r,lhs,rhs) ← relation_lhs_rhs body,
        (lhs,rhs) ← pure $ if pr.reverse then (rhs,lhs) else (lhs,rhs),
        -- tactic.trace_m "convert: " $ lhs,
        tactic.unify e lhs,
        rest ← close_obvs_goals ms,
        guard (rest.length = 0), -- [todo] sometimes a variable won't be filled eg in coannihilation moves.
        type ← infer_type lhs,
        lhs ← instantiate_mvars lhs,
        rhs ← instantiate_mvars rhs,
        -- tactic.trace_m "convert: " $ pr.ctxt,
        pf ← (mk_app pr.pf $ list.reverse ms) >>= instantiate_mvars,
        -- tactic.trace_m "convert: " $ lhs,
        pure $ {rule . type := type, rel := ⟨r,pr.reverse⟩, params := [], lhs:=lhs, rhs:=rhs, pf := pf}
    open tactic

end prerule

meta def prerule_table := tabledict name prerule

namespace prerule_table

local attribute [reducible] prerule_table

meta instance : has_emptyc prerule_table := infer_instance
meta instance : has_union prerule_table := infer_instance

meta def insert : prerule → prerule_table → prerule_table
| p t := tabledict.insert p.get_key p t

meta instance : has_insert prerule prerule_table := ⟨insert⟩

meta structure config :=
(wilds := ff)

meta def head_rewrites (lhs : expr) (rt : prerule_table) (cfg : config := {}) : tactic (list rule) := do
    let k := expr_table.get_key lhs,
    let wilds := if cfg.wilds then tabledict.get `rule_table.wildcard rt else ∅,
    let keyed := tabledict.get k rt,
    let t := wilds ∪ keyed,
        kpp ← pp k, tpp ← pp t,
    --  trace $ ("getting key ":format) ++ kpp ++ " with rules " ++ tpp,
    results ← t.mfold (λ acc pr, (do
        ppr ← to_string <$> pp pr,
        -- tactic.trace_m "hr: " $ ppr,
        r ← prerule.convert lhs pr,
        -- tactic.trace_m "hr: " $ r,
        pure $ list.cons r acc
        ) <|> pure acc
    ) [],
    -- tactic.trace_m "hr: " $ results,
    pure results

private meta def rewrites_aux (rt : prerule_table) (cfg : config := {})
: zipper → list (rule × zipper.path) → tactic (list (rule × zipper.path))
|z acc := do
    ppz ← to_string <$> pp z,
    hrs ←
        -- timetac ("head_rewrites: " ++ ppz) $
        head_rewrites z.cursor rt cfg,
    -- tactic.trace_m "rewrites_aux: " $ hrs,
    -- hrs ← list.mchoose (λ rw, head_rewrite rw z) hrs,
    hrs ← pure $ hrs.map (λ r, (r,z.get_path)),
    acc ← pure $ hrs ++ acc,
    ⟨f,children⟩ ← down_proper z,
    acc ← children.mfoldl (λ acc z, rewrites_aux z acc) acc,
    pure acc

meta def head_rewrites_at (rt : prerule_table) (e : expr) (a : address) (cfg : config := {}) : tactic (list rule) := do
    z ← zipper.down_address a $ zipper.zip $ e,
    head_rewrites z.cursor rt cfg

-- [TODO] wildcard moves should have their own section, since one is constructed for each node in the tree.
-- [TODO] similarly, anti-annihilator moves (moves which have metas after matching) should be put in their own section.
/-- Returns head rewrites for each proper subterm of the given expression, and then returns the raw rule that is applied there along with a
zipper path to the application site for lhs. -/
meta def rewrites (lhs : expr) (rt : prerule_table) (cfg : config := {}) : (tactic $ list (rule × zipper.path)) :=
rewrites_aux rt cfg (zipper.zip lhs) []

meta instance : has_to_tactic_format prerule_table := tabledict.has_to_tactic_format

end prerule_table


end hp