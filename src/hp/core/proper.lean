import basic hp.core.hyp hp.core.stub
namespace hp
open expr expr.zipper tactic

/-!

# Proper arguments

In order to make convincing writeups of the function, it is necessary to define the notion of a 'proper'
argument to a function.

A proper argument is an argument to a function that is not implicit, a typeclass instance or a proposition.
This is not quite the same as `is_term`, since we can have terms that are implicit arguments.

-/

/-- A proper argument is one who is not implicit or a proposition.
    Ie, anything which the user would see when writing down the term. -/
private meta def is_proper (p : param_info) : bool :=
    ¬(param_info.is_implicit p || param_info.is_inst_implicit  p || param_info.is_prop p)

meta def is_type (z : zipper) : tactic bool := expr.is_sort <$> tactic.infer_type z.cursor

/-- Take a zipper where the cursor expression is a function application,
    and return zippers over all of the non-implicit, non-prop arguments. -/
meta def down_proper (z : zipper) : tactic (zipper × list zipper) := do
    let c := z.cursor,
    let f := expr.get_app_fn c,
    let f_name := expr.as_name f,
    -- if it is a numeral then don't expand it.
    if f_name = `bit0 ∨ f_name = `bit1 then pure (z,[]) else do
    let args := expr.get_app_args c,
    params ← (fun_info.params <$> tactic.get_fun_info f (args.length)) <|> pure [],
    let params := list.reverse params,
    ⟨zippers, fz⟩ ← params.mfoldl (λ acc p, do
            let (⟨zippers,z⟩ : (list zipper) × zipper) := acc,
            z' ← down_app_fn z,
            if is_proper p then do
                zr ← down_app_arg z,
                --t ← is_type zr,
                --if t then pure (zippers,z') else
                pure (zr::zippers,z')
            else pure (zippers, z')
        )
        (([] : list zipper), z),
    pure (fz,zippers)

/-- [todo] should do the opposite of down_proper. -/
meta def up_proper (z : zipper) : tactic zipper := z.up

/-- Traverse zipper.current, only exploring explicit, non-Prop arguments.
    If `f` fails, then that branch is skipped. -/
meta def traverse_proper {α} (f : α →  zipper → tactic α) : α → zipper → tactic α
|a z := (do
    a ← f a z,
    (_,children) ← down_proper z,
    children.mfoldl traverse_proper a)
    <|> pure a

meta def get_shared_nodes : zipper → zipper → tactic (list expr)
| z₁ z₂ := do
    (f₁,cs₁) ← down_proper z₁,
    (f₂,cs₂) ← down_proper z₂,
    if f₁.cursor ≠ f₂.cursor ∨ f₁.cursor.is_mvar ∨ cs₁.length ≠ cs₂.length then pure [] else do
    cs ← pure $ list.zip cs₁ cs₂,
    rs ← cs.mcollect (λ ⟨c₁,c₂⟩, get_shared_nodes c₁ c₂),
    pure $ (f₁.cursor) :: rs

meta def get_symbols : zipper → tactic (list expr)
| z := do
    -- trace_m "get_symbols: " $ z.current,
    (f, children) ← down_proper z,
    symbols ← children.mcollect get_symbols,
    if not f.cursor.is_mvar then pure $ f.cursor :: symbols else pure symbols

/-- `minimal_monotone p z` finds the smallest proper subexpressions of the zipper such that
    `p` doesn't fail.
    [NOTE] It assumes that if `p e` fails, then all of `e`s subexpressions will fail too. -/
meta def minimal_monotone {α} (p : zipper → tactic α) : zipper → tactic (list α)
|z := (do
        a ← p z,
        (_,children) ← down_proper z,
        kids ← list.join <$> list.mmap minimal_monotone children,
        pure $ list.cases_on kids [a] (λ _ _,kids)
    )
    <|>  pure []

/-- `maximal_monotone p z`: Find the largest proper subexpressions of the zipper such that
    `p` doesn't fail.
    [NOTE] It assumes that if `p e` fails, then all of `e`s subexpressions will fail too. -/
meta def maximal_monotone {α} (p : zipper → tactic α) : zipper → tactic (list α)
|z := (do a ← p z,  pure [a]) <|> do
        (f,children) ← down_proper z,
        children ← pure $ if is_local_constant f && ¬children.empty then list.cons f children else children,
        kids ← list.join <$> list.mmap maximal_monotone children,
        pure $ kids

/-- `find_occurences z e` finds subexpressions of `z` which non-trivially unify with `e`. -/
meta def find_occurences : zipper → expr → tactic (list zipper) := λ E e, do
    rs ← maximal_monotone (λ z, do
        if z.is_mvar || z.is_constant then failure else do
        -- trace_m "find_occurences: " $ (e,z),
        ((tactic.hypothetically (unify e z.cursor transparency.none)) *> pure z)
    ) E,
    pure rs

meta def has_occurences : zipper → expr → tactic bool
| z e := (bnot ∘ list.empty) <$> find_occurences z e


private meta def smallest_absent_subterms_aux (l : expr)
    (filter : zipper → tactic bool := combinator.K $ pure tt)
    : list expr.address  → zipper → tactic (list expr.address × list (ℕ × zipper))
|used z := do
    filt ← filter z,
    if ¬ filt then pure (used, []) else do
    occs ← find_occurences l z.cursor,
    o ← pure $ list.find (λ o, bnot $ list.any used $ λ x, zipper.get_address o < x) occs,
    match o with
    |none := do -- z.current is not present, descend.
        (_,children) ← down_proper z,
        (used,zs) ← list.mfoldl (λ p child, do
            (used,zs') ← smallest_absent_subterms_aux (prod.fst p) child,
            pure (used,zs' ++ p.2)
        ) (used,[]) children,
        if zs.empty then pure $ (used,[(occs.length + 1,z)]) else pure $ (used,zs)
    |(some o) :=
        -- z.cursor is present on the lhs
        -- so now we need to add `o` to the used list so that later matches can't use it.
        pure $ (used.insert o.get_address,[])
    end
/-- Returns ff if all of the local variables in the cursor of the zipper are type or typeclass local_consts. -/
private meta def no_local_const_terms : zipper → tactic bool
:= λ z, list.empty <$> (list_local_const_terms $ cursor $ z)
/-- find subterms of y that do not appear on x. It will also count when occurrences have been used.
    So for example, ``smallest_absent_subterms `(a * b + b * a) `(a * b + a * b)`` will return `[(2,a * b)] because
    `a * b` occurs once in x but twice in y.
    It also ignores term subexpressions that do not contain local constants.
-/
meta def smallest_absent_subterms (x : expr) (y : zipper) :=
    prod.snd <$> smallest_absent_subterms_aux x (λ z, bnot <$> no_local_const_terms z) [] y

meta def smallest_absent_composite_subterms (lhs : expr) (rhs : zipper) :=
    prod.snd
        <$> smallest_absent_subterms_aux lhs
            (λ s, do
                hlcst ← bnot <$> no_local_const_terms s,
                is_term ← is_term s.cursor,
                    pure $ hlcst && is_term && expr.is_composite s.cursor)
            [] rhs

meta def dummify_replace_core (replacement : expr) : expr → expr → nat → option expr
| (expr.mvar u _ _) (expr.mvar u2 _ _) _ := if u = u2 then some replacement else none
| `(classical.some %%x) `(classical.some %%y) _ := do
    f1 ← some $ get_app_fn x,
    f2 ← some $ get_app_fn y,
    if f1 = f2 then some replacement else none

| _ _ _ := none

/-- The pretty printer will automatically instantiate vars which leads to an issue where
earlier clauses will talk about variables that later get assigned.
The 'dummifier' solves this by replacing instantiated metavariables with dummy undeclared
variables before they are pretty printed.
-/
meta def dummify {α} [assignable α] : (expr × name) → α → tactic α
| ⟨ms, n⟩ x := do
    y ← tactic.infer_type ms,
    l ← mk_local' n binder_info.default y,
    r ← assignable.mmap_children (λ Γ e, do
        e' ← pure $ expr.replace e (dummify_replace_core l ms),
        -- if e ≠ e' then trace_m "dummify: " $ ((ms, n), (e, e')) else pure (),
        pure e'
    ) [] x,
    pure r
    -- assignable.mmap_children (λ Γ e, do
    --     e' ← kabstract ms e transparency.reducible ff,
    --     deps ← kdepends_on ms e transparency.reducible,
    --     e'' ← pure $ expr.instantiate_var e' l,
    --     tactic.trace_m "dummify: " (ms, n, e, e''),
    --     pure e
        --  de ← hypothetically (is_success $ tactic.is_def_eq e ms),
        --  pure if de then l else e
    --   if e = ms then some l else none
    --   match e with
    --   | (expr.mvar un pn y) :=
    --         ms.mfirst (λ m,
    --               if un = m.uniq_name then
    --                 trace ("dummify_mvars " ++ m.pretty_name.to_string) $
    --                 some $ expr.local_const m.uniq_name m.pretty_name binder_info.default m.type
    --               else none )
    --   | _ := none
    --   end
-- ) [] x

/-- Attempt to solve the main goal with assumption. Will fail if the main goal is not a prop. -/
meta def prop_assumption : tactic unit := do
    isp ← target >>= is_prop,
    if isp then assumption else fail "target not a Prop"

/-- Try to close all the given mvars with either apply_instance or an assumption.
Returns the sublist that could not be closed. -/
meta def close_obvs_goals : list expr → tactic (list expr) | e := do
    gs ← get_goals,
    set_goals e,
    all_goals $ try $ (apply_instance <|> prop_assumption),
    ms ← get_goals,
    set_goals gs,
    pure ms

/--`lowest_uncommon_subterms l z` finds the smallest subterms of z that are not a subterm of `l`. Subterms must include a local_const -/
meta def lowest_uncommon_subterms (l : expr) (z : zipper) :=
    minimal_monotone (λ z,
        if z.is_mvar || z.is_constant || ¬ z.has_local then failure else do
        --let o := expr.occurs z.cursor l,
        matches ← maximal_monotone (λ rz, (tactic.hypothetically $ unify z.cursor rz.cursor) ) $ zipper.zip l,
        -- trace_m "lus: " $ (z,l,o, matches),
        if ¬ matches.empty then failure else pure z
    ) z

meta def largest_common_subterms (z₁ z₂ : zipper): tactic (list zipper) :=
    list.join <$> maximal_monotone (λ z₁,
        if z₁.is_mvar then failure else do
        ocs ← find_occurences (z₂) z₁.cursor,
        if ocs.empty then failure else pure ocs
    ) z₁

private meta def get_functions_aux : list expr → zipper → tactic (list expr)
| acc z := do
    (f,zs) ← down_proper z,
    if zipper.is_mvar f then pure acc else
    zs.mfoldl get_functions_aux $ insert f.cursor acc

meta def count_symbols : expr → tactic (list expr) := get_functions_aux ∅ ∘ zip

meta def does_unify (e : expr) : zipper → tactic unit
| z := if z.is_mvar then failure else
    (tactic.hypothetically $ unify e z.cursor transparency.none ff)

meta def find_subterms (e : expr) : zipper → tactic (list zipper)
:= traverse_proper (λ acc z, (does_unify e z *> pure (z::acc)) <|> pure acc) []

meta def has_single_subterm (e : expr) : zipper → tactic (zipper)
:= λ z, do [x] ← find_subterms e z, pure x

meta def count_subterms (e : expr) : zipper → tactic ℕ
:= λ z, do xs ← find_subterms e z, pure $ list.length xs

meta def find_non_unify_subterm (e : expr) : zipper → tactic zipper
|z :=
    if e = z.cursor then pure z else do
    (_,zs) ← down_proper z,
    list.mfirst find_non_unify_subterm zs

meta def find_subterm (e : expr) : zipper → tactic zipper
|z :=
    (does_unify e z *> pure z)
    <|> do
        (_,zs) ← down_proper z,
        list.mfirst find_subterm zs

meta def distance_to_subterm_down (e : expr) : zipper → nat → tactic nat
|z d :=
    if z.is_mvar then failure else
    (tactic.hypothetically $ (do
        unify e z.cursor,  pure d
    ))
    <|> (do
        -- tactic.trace_m "dtsd: " $ z,
        (_,zs) ← down_proper z,
        list.mfirst (λ iz : ℕ × zipper, distance_to_subterm_down iz.2 $ iz.1 + d + 1)
        $ list.with_indices zs
    )

meta def right : zipper → option zipper
|z := if is_app_arg z then up z >>= right else up z >>= down_app_arg

meta def distance_to_subterm_up (e : expr) : ℕ → zipper → tactic ℕ
|d z :=
    if is_app_arg z then up z >>= distance_to_subterm_up (d+1) else do
    -- tactic.trace_m "dtsu1: " $ z,
    z ← up z >>= lift down_app_arg,
    -- tactic.trace_m "dtsu2: " $ z,
    distance_to_subterm_down e z (d+1)
    <|> distance_to_subterm_up (d+1) z

meta def get_distance (outer : expr) (l : expr) (r : expr) : tactic ℕ := do
    outer ← tactic.instantiate_mvars outer,
    first ← find_subterm l outer,
    -- tactic.trace_m "gd: " $ first,
    distance_to_subterm_up r 0 first

meta def get_proper_children (e : expr) : tactic (list expr) := do
    e ← tactic.instantiate_mvars e,
    (list.map cursor <$> prod.snd <$> (down_proper $ zip e)) <|> pure []

meta def get_smallest_complex_subterms (z : zipper) : tactic (list zipper) := do
    minimal_monotone (λ z, do ⟨_,[]⟩ ← down_proper z | failure, pure z) z


/-- `does_match l r` Returns true if the left item's mvars can be filled in to be defeq with `r` -/
meta def does_match : expr → expr → tactic bool
| l r := (do
    l' ← tactic.hypothetically (do
        unify l r transparency.none,
        tactic.instantiate_mvars l
    ),
    pure $ l = l') <|> pure ff



end hp