import basic hp.core

namespace hp

/-- A relation and a directionality.
So eg `<` is encoded as `⟨has_lt, ff⟩` and `>` is encoded as `⟨has_lt, tt⟩`.
`=` is encoded as `⟨eq,ff⟩`.
-/
@[derive decidable_eq]
meta structure rel_inst :=
(r : name)
(dir : bool)

meta def rel_inst.op : name → tactic name
| `eq := pure `eq
| _ := failure

meta def rel_inst.mk_app : rel_inst → expr → expr → tactic expr
| ⟨n,ff⟩ l r := tactic.mk_app n [l,r]
| ⟨n,tt⟩ l r := do n ← rel_inst.op n, tactic.mk_app n [l,r]

meta def rel_inst.flip : rel_inst → rel_inst | ⟨n,d⟩ := ⟨n,bnot d⟩

meta instance : has_coe name rel_inst := ⟨λ n, ⟨n,ff⟩⟩

/-- A `rule` is a lemma of the form `pf : Π ..params, rel lhs rhs`. The parameters `params` should all be concrete.
That is, have types that are not dependent on other parameters.
The effects of setting `rel_inst.dir`:
For example, with `dir := false`, we have
`lhs ≤ rhs`
and with dir true we have `lhs ≥ rhs` or equivalently `rhs ≤ lhs`.
The dir says that we should flip the ordering of lhs and rhs when using the proof term, but that we
 should still consider lhs to be on the left for the purposes of rule composition and rewriting.
 rewrites always occur lhs -> rhs.
-/
@[derive decidable_eq]
meta structure rule :=
(type : expr) -- the type of LHS and RHS.
(rel : rel_inst)
(params : list expr) -- a list of local constants which lhs and rhs and type are in terms of.
(lhs : expr)
(rhs : expr)
(pf : expr) -- if rel_inst.dir then reverse lhs and rhs before feeding to proof. each param is a pi binding

open expr expr.zipper

namespace rule

meta instance : has_lt rule := ⟨λ x y, x.pf < y.pf⟩

meta instance : decidable_rel ((<) : rule → rule → Prop) := by apply_instance

meta def of_proof : expr → tactic rule
| pf := do
    T ← infer_type pf,
    (ctxt, body) ← pure $ telescope.of_pis T,
    locals ← telescope.to_locals ctxt,
    body ← pure $ expr.instantiate_vars body locals,
    (rel_name, lhs, rhs) ← tactic.relation_lhs_rhs body,
    type ← tactic.infer_type lhs,
    pure { type := type
         , rel := rel_inst.mk rel_name ff
         , lhs := lhs
         , rhs := rhs
         , params := locals
         , pf := expr.mk_app pf $ list.reverse locals
         }

meta def flip : rule → rule
| r := {rel := r.rel.flip, lhs := r.rhs, rhs := r.lhs, ..r}

meta def get_lhs_rhs : rule → tactic (expr × expr)
| r := pure $ (r.lhs, r.rhs)

meta def body : rule → tactic expr
| r := tactic.mk_app r.rel.r $ if r.rel.dir then [r.rhs, r.lhs] else [r.lhs, r.rhs]

meta instance rule_has_to_tactic_format : has_to_tactic_format rule :=
⟨λ r, rel_inst.mk_app r.rel r.lhs r.rhs >>= tactic.pp⟩

meta def of_name (n : name) : tactic rule :=
tactic.resolve_name n >>= pure ∘ pexpr.mk_explicit >>= tactic.to_expr >>= of_proof

meta def is_commute_raw : expr → expr → option expr
| (expr.app (expr.app f1 x1) y1) (expr.app (expr.app f2 x2) y2) := do
    guard $ f1 = f2 ∧ x1 = y2 ∧ y1 = x2, pure f1
| _ _ := none

meta def is_commutativity (r : rule) : option expr := is_commute_raw r.lhs r.rhs

meta def is_ground (r : rule)  : bool  := r.params.empty

/-- Returns true when the left hand side is a variable or metavariable. -/
meta def lhs_wildcard : rule → bool := λ r, expr.is_var r.lhs || expr.is_mvar r.lhs

/-- Returns true when the right hand side is a variable or metavariable. -/
meta def rhs_wildcard : rule → bool := λ r, expr.is_var r.rhs || expr.is_mvar r.rhs

meta def with_metas : rule → tactic (list expr × rule) | r := do
    ms ← r.params.mmap (λ lc, do
        m ← (tactic.mk_meta_var $ expr.local_type lc),
        pure (expr.local_uniq_name lc, m)
    ),
    c ← pure $ { rule
                . params := []
                , rel := r.rel
                , type := r.type
                , lhs := instantiate_locals ms r.lhs
                , rhs := instantiate_locals ms r.rhs
                , pf :=  instantiate_locals ms r.pf
                },
    pure (prod.snd <$> ms, c)

meta def instantiate_mvars : rule → tactic rule | r := do
    lhs ← tactic.instantiate_mvars r.lhs,
    rhs ← tactic.instantiate_mvars r.rhs ,
    pf ← tactic.instantiate_mvars r.pf,
    pure $ { lhs := lhs, rhs := rhs, pf := pf , ..r}

meta def mk_trans_proof : expr → expr → tactic expr |p₁ p₂ := tactic.mk_sorry

open tactic

meta def instantiate_params : rule → list expr → tactic rule | r assignments := do
    let zipples := list.zip (expr.local_uniq_name <$> r.params) assignments,
    pure {rule
         . lhs := instantiate_locals zipples r.lhs
         , rhs := instantiate_locals zipples r.rhs
         , pf := instantiate_locals zipples r.pf
         , params := [], ..r }

/-- Take a path entry and compute the right equality congruence rule to use. -/
private meta def mk_congr : expr → zipper.path.entry → tactic expr
| pf (zipper.path.entry.app_fn () a) := tactic.mk_congr_fun pf a
| pf (zipper.path.entry.app_arg f ()) := tactic.mk_congr_arg f pf
| pf _ := fail "rewriting under binders not implemented"

meta def make_congr_proof : expr → expr.zipper.path → tactic expr
| pf z := z.mfoldl mk_congr pf

meta def mk_monotone_proof : expr → zipper → tactic expr
| pf z := tactic.mk_sorry

-- meta def head_rewrite : rule → zipper → tactic rule
-- |r z := do
--     guard (r.rel.r = `eq),
--     pf ← make_congr_proof r.pf z,

open tactic

/-- Take an unparameterised rule - that is, a rule with params = [] - and
    take a list of metavariable, local_const pairs and assign each unassigned mvar in the list to a new local_constant.
    then return a rule with these new local constants as its parameters. -/
private meta def reparameterise : list (expr × expr) → rule → tactic rule | ps r := do
        let mmapper := (λ (p : expr×expr), do
            ⟨m,expr.local_const u_n pp_n bi y⟩ ← pure p,
            ia ← tactic.is_assigned m <|> pure ff,
            if ia then pure m else do
            loc' ← tactic.mk_local' pp_n bi y,
            tactic.unsafe.assign m loc',
            pure loc'
        ),
        ms ← list.mmap mmapper $ ps,
        locals ← pure $ list.bfilter expr.is_local_constant ms,
        ms ← ms.mmap tactic.instantiate_mvars,
        r ← rule.instantiate_mvars r,
        pure {
            params := locals,
            ..r
        }

meta def same_statement : rule → rule → tactic bool |r1 r2 :=
    if r1.params.length ≠ r2.params.length then pure ff else do
    -- [todo] if dirs are different and the rel is non-symmetric then fail.
    if r1.rel.r ≠ r2.rel.r then pure ff else do
    tactic.hypothetically (do
        r3 ← instantiate_params r1 r2.params,
        pure $ (r3.lhs = r2.lhs) && (r3.rhs = r2.rhs)
    ) <|> pure ff

meta def compose : rule → rule → tactic (list rule) | r1 r2 := do
    tactic.hypothetically (do
        (ms1,mr1) ← with_metas r1,
        (ms2,mr2) ← with_metas r2,
        unify mr1.rhs mr2.lhs,
        ps ← pure $ list.zip (ms1 ++ ms2) (r1.params ++ r2.params),
        pf ← mk_trans_proof  mr1.pf mr2.pf,
        r ← pure {rule . type := r1.type, rel := r1.rel, lhs := mr1.lhs, rhs := mr2.rhs, params := [], pf := pf},
        r ← reparameterise ps r,
        pure [r]
    ) <|> pure []

meta structure subcomposition :=
(l : rule)
(r : rule)
(rz : zipper)
(l_assignments : list expr)
(r_assignments : list expr)
(intersection_symbols : list expr)
(new_rule : rule)

/-- Take a pair of rules `lc`, `rc` and find a subterm of lc.rhs that unifies with rc.lhs and then compose them.
 -/
meta def subcompose (lc : rule) (rc : rule) : tactic (list subcomposition) := do
    tactic.hypothetically (do
        (lm,l) ← with_metas lc,
        (rm,r) ← with_metas rc,
        results ← hp.traverse_proper (λ acc z, do -- [todo] replace 'traverse_proper' with traverse monotone.
            if zipper.is_mvar z then pure acc else do
            tactic.hypothetically (do
                unify r.lhs z.cursor transparency.none,
                -- trace_m "subcompose: " $ (lc, rc),
                pf ← tactic.mk_sorry, -- [hack] [todo] get below line to work.
                -- pf  ← make_congr_proof r.pf z >>= mk_trans_proof l.pf,
                new_rule ← pure { rule
                          . type := l.type
                          , params := []
                          , rel := l.rel -- [todo] get from transitivity lemma
                          , lhs := l.lhs
                          , rhs := z.unzip_with r.rhs
                          , pf := pf
                          },
                ps ← pure $ list.zip (lm ++ rm) (lc.params ++ rc.params),
                new_rule ← reparameterise ps new_rule,
                lm ← lm.mmap tactic.instantiate_mvars,
                rm ← rm.mmap tactic.instantiate_mvars,
                intersection_symbols ← hp.get_shared_nodes r.lhs z,
                sc ← pure $ { subcomposition
                             . l := lc
                             , r := rc
                             , rz := z
                             , l_assignments := lm
                             , r_assignments := rm
                             , intersection_symbols := intersection_symbols
                             , new_rule := new_rule
                             },
                pure $ list.cons sc acc
            ) <|> pure acc
        ) [] $ zipper.zip l.rhs,
        pure results
    )

meta def subsume : rule → rule → tactic (list rule)
| r1 r2 := do
    ss ← same_statement r1 r2,
    if ss then pure [] else do
    tactic.hypothetically (do
            (ms1,mr1) ← with_metas r1,
            (ms2,mr2) ← with_metas r2,
            unify mr1.lhs mr2.lhs,
            unify mr1.rhs mr2.rhs,
            ps ← pure $ list.zip (ms1 ++ ms2) (r1.params ++ r2.params),
            r ← reparameterise ps mr1,
            pure [r]
    ) <|> pure []

-- /-- Get the smallest terms on the lhs of rule which are not present on the rhs. [todo] rename to not be confused with `get_destroys`. -/
-- meta def get_destructions (r : rule) : tactic (list zipper) := do
--     (lhs,rhs) ← rule.get_lhs_rhs r,
--     destroys ← minimal_monotone (λ z_lhs, do
--         occs ← find_occurences rhs z_lhs.cursor,
--         guard (occs.empty),
--         pure z_lhs
--     ) lhs,
--     pure destroys

-- /-- Get the smallest terms on the lhs of rule which are not present on the rhs. -/
-- meta def get_creations (r : rule) : tactic (list zipper) := do
--     (lhs,rhs) ← rule.get_lhs_rhs r,
--     creates ← minimal_monotone (λ z_rhs, do
--         occs ← find_occurences lhs z_rhs.cursor,
--         guard (occs.empty),
--         pure z_rhs
--     ) rhs,
--     pure creates

meta def get_creates_aux (rev : bool) : expr → rule → tactic (list rule)
| e r := do
    (ms,mr) ← rule.with_metas r,
    /- idea: `r` creates `e` when there exists a substitution σ such that e ∉ lhs and e ∈ rhs.
       additionally, `e` can't appear in σ. A part of `e` must be non-trivially involved in the rewrite.
    -/
     (lhs,rhs) ← (if rev then prod.swap else id) <$> get_lhs_rhs r,
     rs ← maximal_monotone (λ rhs,
        if rhs.is_mvar || rhs.is_constant then failure else do
        tactic.hypothetically (do
            unify e rhs.cursor transparency.none,
            occs ← find_occurences lhs e, -- [todo] likely optimisable
            guard $ occs.empty,
            r ← reparameterise (list.zip ms mr.params) mr,
            pure r
        )
     ) rhs,
    pure rs

meta def head_rewrite : expr → rule → tactic rule
| e rc := do
    (rm,r) ← with_metas rc,
    tactic.hypothetically (do
        unify e r.lhs,
        ps ← pure $ list.zip rm rc.params,
        new_rule ← reparameterise ps r,
        -- trace_m "head_rewrite: " $ new_rule,
        pure new_rule
    )

meta def congr : zipper.path → rule → tactic rule
| p r := do
   lhs ← pure $ zipper.path.apply p r.lhs,
   rhs ← pure $ zipper.path.apply p r.rhs,
   type ← tactic.infer_type lhs,
   pf ← make_congr_proof r.pf p,
--    trace_m "congr: " $ lhs,

   pure $ { rule
     . type := type
     , rel := r.rel -- [todo] in general this needs to be deduced from monotone lemmas
     , params := r.params
     , lhs := lhs
     , rhs := rhs
     , pf := pf
     }

/-- moves up a zipper path until the rule can be applied. -/
meta def rewrite_on_zipper (r : rule) : zipper → tactic rule
| z := (head_rewrite z.cursor r >>= congr z.get_path) <|> (up z >>= rewrite_on_zipper)

meta def get_creates := get_creates_aux tt
meta def get_destroys := get_creates_aux ff

-- [todo] another case is an 'independent subcompose'. This is where you rw on a param in the upper rule. This also should require a 'target expression' to prevent too many cases from being made.
/- That is,
    a pair r₁, r₂ such that r₁(_,_,r₂,_,_).rhs =?= target and the lhs doesn't and r₁ independently doesn't.
    It might also have to be that a subterm of the RHS unifies in a way that crosses the region between r₁ r₂.
    It will be best to figure this out when I have some specific examples when the above methods are not good enough.
 -/

meta def mmap_children {t : Type → Type} [monad t] (f : telescope → expr → t expr) : telescope → rule → t rule
| Γ r := pure rule.mk
            <*> (Γ ⍄ f $ r.type)
            <*> pure r.rel
            <*> (Γ ⍄ f $ r.params) -- [bug] is this right?
            <*> (Γ ⍄ f $ r.lhs)
            <*> (Γ ⍄ f $ r.rhs)
            <*> (Γ ⍄ f $ r.pf)

meta instance : assignable rule := ⟨@mmap_children⟩

meta def is_def_eq (r₁ r₂ : rule) : tactic bool :=
  tactic.is_success $ (do
    tactic.is_def_eq r₁.lhs r₂.lhs,
    tactic.is_def_eq r₁.rhs r₂.rhs
  )

meta def lhs_param_at : address → rule → bool
| a r := ff <| (do s ← expr.address.follow a r.lhs,
    pure $ (expr.is_local_constant s) ∧ (r.params.any (λ x, s = x)))

-- /-- Alternative implementation of congr using rewrite instead of mk_congr. -/
-- meta def mk_eq_congr : rule → zipper.path → tactic rule
-- | r p := do
--     guard (r.rel.r = `eq),
--     new_type ← tactic.to_expr ```(%%(zipper.unzip ⟨p,r.lhs⟩) = %%(zipper.unzip ⟨p,r.rhs⟩)),
--     new_type ← pure $ expr.pis r.params new_type,
--     pf ← tactic.fabricate new_type (do
--         xs ← intron r.params.length,
--         tactic.rewrite_target r.pf
--     ),
--     rule.of_proof pf

/-- Use the given rule application on the lhs of the target. Will look for congruences. -/
meta def rewrite_conv : rule → conv unit := λ r, do
        lhs ← conv.lhs >>= tactic.instantiate_mvars,
        sub ← tactic.instantiate_mvars r.lhs,
        l ← find_occurences (zipper.zip lhs) r.lhs,
        (z::rest) ← pure l,
        r ← tactic.trace_fail $ rewrite_on_zipper r z,
        -- tactic.trace_m "rewrite_conv: " $ r,
        transitivity,
        apply r.pf,
        -- trace_state, trace r,
        try $ all_goals $ apply_instance <|> prop_assumption,
        pure ()

/-- Checks whether the given rule is a local hyp or derived from one. -/
meta def is_local_hypothesis : rule → tactic bool
| r := (do
    p ← pure $ r.pf,
    ls ← pure $ list_locals p,
    ls ← ls.m_some (λ l, (do
        y ← tactic.infer_type l,
        (`=,_,_) ← tactic.relation_lhs_rhs y,
        pure tt) <|> pure ff
    ),
    pure tt
) <|> pure ff

meta def count_metas : rule → tactic nat
| r := do
    lhs ← tactic.instantiate_mvars r.lhs,
    uns ← traverse_proper (λ t e, pure $
        match expr.as_mvar e.cursor with
        | none := t
        | (some ⟨u,_,_⟩) := table.insert u t
        end) ∅ lhs,
    pure $ table.size $ uns

end rule
end hp