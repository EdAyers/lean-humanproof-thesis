import .assignable .expr .tactic
open expr tactic

private meta def products : list expr → pexpr
| [] := ```(unit)
| [x] := to_pexpr x
| (h :: t) := ```(prod %%h %%(products t))

private meta def tuples : list pexpr → pexpr
| [] := ```(unit.star)
| [x] := x
| (h :: t) := ```(prod.mk %%h %%(tuples t))

meta def make_setters (n : name) : tactic unit := do
  gs ← get_goals,
  e ← get_env,
  [c] ← pure $ environment.constructors_of e n | fail "expecting only one constructor to make setters",
  d ← tactic.returnex $ environment.get e c,
  (bs, b) ← pure $ telescope.of_pis d.type,
  ls ← telescope.to_locals bs,
  b ← pure $ b.instantiate_vars $ ls,
  params ← pure $ list_locals b,
  bs' ← pure $ telescope.of_locals params,
  param_names ← pure $ list.reverse $ params.map local_uniq_name,
  fields ← pure $ ls.filter (λ l, l ∉ params),
  fields ← pure $ fields.reverse,
  fields.mmapi (λ i field, do
    is_trm ← tactic.is_term field,
    f_name ← pure $ expr.local_pp_name field,
    if ¬(is_trm) then pure () else do
    field_type ← infer_type field,
    out ← to_expr ```(%%field_type → %%b → %%b),
    out ← pure $ abstract_locals out param_names,
    y ← pure $ telescope.to_pis out bs',
    name.mk_string base_name rest ← pure f_name,
    setter_name ← pure $ name.mk_string ("with_" ++ base_name) n,
    v ← mk_meta_var y,
    set_goals [v],
    tactic.intron params.length,
    x ← tactic.intro `x,
    o ← tactic.intro `o,
    [⟨_,args⟩] ← tactic.cases o,
    tactic.split,
    gs' ← get_goals,
    (_,args) ← pure $ list.split_at (args.length - gs'.length) args,
    args.mmapi (λ j arg, do
      if i = j then tactic.exact x else tactic.exact arg
    ),
    v ← instantiate_mvars v,
    add_decl $ declaration.defn setter_name d.univ_params y v (reducibility_hints.abbrev) (d.is_trusted),
    set_goals gs,
    pure ()
  ),
  fields.mmapi (λ i field, do -- [todo] make DRY.
    is_trm ← is_term field,
    f_name ← pure $ expr.local_pp_name field,
    if ¬(is_trm) then pure () else do
    field_type ← infer_type field,
    out ← to_expr ```((%%field_type → %%field_type) → %%b → %%b),
    out ← pure $ abstract_locals out param_names,
    y ← pure $ telescope.to_pis out bs',
    name.mk_string base_name rest ← pure f_name,
    setter_name ← pure $ name.mk_string ("modify_" ++ base_name) n,
    v ← mk_meta_var y,
    set_goals [v],
    tactic.intron params.length,
    x ← tactic.intro `x,
    o ← tactic.intro `o,
    [⟨_,args⟩] ← tactic.cases o,
    tactic.split,
    gs' ← get_goals,
    (_,args) ← pure $ list.split_at (args.length - gs'.length) args,
    args.mmapi (λ j arg, do
      if i = j then tactic.exact (expr.app x arg) else tactic.exact arg
    ),
    v ← instantiate_mvars v,
    add_decl $ declaration.defn setter_name d.univ_params y v (reducibility_hints.abbrev) (d.is_trusted),
    set_goals gs,
    pure ()
  ),
  set_goals gs,
  interactive.trivial,
  pure ()

/-- Given the name of an inductive datatype will make `as_x` and `is_x` for each constructor x. -/
meta def make_prisms (n : name) : tactic unit := do
  gs ← get_goals,
  e ← get_env,
  cs ← pure $ environment.constructors_of e n,
  cs.mmap (λ cn, do
    d ← tactic.returnex $ environment.get e cn,
    (bs, b) ← pure $ telescope.of_pis d.type,
    ls ← telescope.to_locals $ bs,
    b ← pure $ b.instantiate_vars $ ls,
    params ← pure $ list_locals b, -- [todo] make DRY
    param_names ← pure $ list.reverse $ params.map local_uniq_name,
    fields ← pure $ ls.filter (λ l, l ∉ params),
    field_types ← list.mmap infer_type $ list.reverse $ fields,
    prods ← to_expr $ products $ field_types,
    prods ← to_expr $ ```(option %%prods),
    prods ← pure $ lift_vars (abstract_locals prods param_names) 0 1,
    b' ← pure $ abstract_locals b param_names,
    bs' ← pure $ telescope.of_locals params,
    y ← pure $ telescope.to_pis (expr.pi `item binder_info.default b' prods) bs',
    name.mk_string base_name rest ← pure cn,
    prism_name ← pure $ name.mk_string ("as_" ++ base_name) rest,
    v ← mk_meta_var y,
    set_goals [v],
    tactic.intron params.length,
    h ← tactic.intro `h,
    cs ← tactic.cases h,
    cs.mmap (λ ⟨cn₂, args⟩, do
      if cn = cn₂ then do
        tups ← pure $ tuples $ list.map (λ _, pexpr.mk_placeholder) field_types,
        refine ```(some %%tups),
        gs ← get_goals,
        -- assuming that the actual fields and not params are at the end?
        (_,args) ← pure $ list.split_at (args.length - gs.length) args,
        args.mmap tactic.exact,
        pure ()
      else do refine ```(none)
    ),
    v ← instantiate_mvars v,
    add_decl $ declaration.defn prism_name d.univ_params y v (reducibility_hints.abbrev) (d.is_trusted),

    set_goals gs,

    -- is_x setter
    prism_name ← pure $ name.mk_string ("is_" ++ base_name) rest,
    y ← pure $ telescope.to_pis (expr.pi `item binder_info.default b' `(bool)) bs',
    w ← mk_meta_var y,
    set_goals [w],
    tactic.intron params.length,
    x ← intro `h,
    applyc `option.is_some,
    apply v,
    apply x,
    w ← instantiate_mvars w,
    add_decl $ declaration.defn prism_name d.univ_params y w  (reducibility_hints.abbrev) (d.is_trusted),

    set_goals gs,
    pure ()
  ),
  set_goals gs,
  interactive.trivial,
  pure ()

meta def prism_user_attr : user_attribute unit unit :=
{ name := `derive_prisms
, descr := "for each constructor `x : α → β → τ` adds a
definition `as_x : τ → option (α × β)` which returns none
if the argument is not an `x` or returns the arguments of
the constructor otherwise"
, after_set := some $ λ n i b, make_prisms n
}

run_cmd attribute.register `prism_user_attr

meta def setters_user_attr : user_attribute unit unit :=
{ name := `derive_setters
, descr := "for each field in a structure add a setter declaration `with : x → y → y` "
, after_set := some $ λ n i b, make_setters n
}

run_cmd attribute.register `setters_user_attr

-- /-  EXAMPLES:  -/

-- #check hello

-- @[derive_setters]
-- structure hello (α : Type): Type :=
-- (foo : string)
-- (asdf : string)
-- (bar : α)

-- #check @hello.with_asdf
-- #eval hello.asdf $ hello.with_asdf "adsf" $ hello.mk "foo" "xxx" 34
-- #eval hello.asdf $ hello.modify_asdf (λ x, "adsf" ++ x) $ hello.mk "foo" "xxx" 34
-- #eval hello.bar $ hello.modify_bar (λ x, 5 + x) $ hello.mk "foo" "xxx" 34
-- #eval hello.foo $ hello.with_asdf "adsf" $ hello.mk "foo" "xxx" 34

-- @[derive_prisms]
-- inductive my_vec (α β : Type) : ℕ → Type
-- |nil {} : β → my_vec (nat.zero)
-- -- |flurm : Π (n : nat),  my_vec n -- [bug] this case fails
-- |cons {n} : α → (ℕ → my_vec n) → my_vec (n+1)

-- #check @my_vec
-- #check @my_vec.cons
-- #check @my_vec.as_nil
-- #check @my_vec.is_nil
-- #check @my_vec.as_cons
-- -- #check @my_vec.as_flurm
-- #eval my_vec.as_nil $ @my_vec.nil nat nat 3
-- #eval my_vec.is_nil $ @my_vec.nil nat nat 3
-- #eval my_vec.is_cons $ @my_vec.cons nat nat 0 5 (λ x, @my_vec.nil nat nat 3)