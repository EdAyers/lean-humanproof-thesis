import .expr_zipper
open tactic
universe u
/-- ltb is the same as lt but it goes to a bool rather than a prop to make deriving decidability easier. -/
class has_ltb (α : Type u) := (ltb : α → α → bool)
instance lt_of_ltb (α : Type u) [has_ltb α] : has_lt α := ⟨λ x y, has_ltb.ltb x y⟩
instance dec_lt_of_ltb (α : Type u) [has_ltb α] : decidable_rel ((<) : α → α → Prop) := by apply_instance
instance le_of_ltb (α : Type u) [has_ltb α] : has_le α := ⟨λ x y, x < y ∨ x = y⟩
instance dec_le_of_ltb (α : Type u) [has_ltb α] [decidable_eq α] : decidable_rel ((≤) : α → α → Prop)  := by apply_instance

namespace derivations
/-- An 'inductive argument' is either just a normal argument or a recursive argument.
So for example `@list.cons {α}` is a constructor with two arguments,
one being a normal with type α and the second being recursive.
-/
meta inductive ind_arg
| normal : expr → ind_arg
| recursive (arg : expr) (rr : expr) : ind_arg

meta def map_ind_arg (f : pexpr → pexpr): ind_arg → pexpr
| (ind_arg.normal e) := f $ to_pexpr e
| (ind_arg.recursive _ rr) := to_pexpr rr

meta def ind_arg.pp : ind_arg → tactic format
| (ind_arg.normal a) := pp a >>= pure ∘ (++ "normal ")
| (ind_arg.recursive a b) := pure (λ a b, "rec " ++ a ++ " " ++ b) <*> pp a <*> pp b

meta instance : has_to_tactic_format ind_arg := ⟨ind_arg.pp⟩

/-- Induction but the induction hypotheses are bundled with their respective arguments.
Contrast this with the result of `induction` where all of the arguments are given, followed by the induction hyps
and you don't know immediately whether you are looking at an ind hyp, a normal arg or a recursive arg.
 -/
meta def induction_but_the_recursors_are_kept_with_the_arguments (x : expr)
    : tactic $ list (name × list ind_arg × list (name × expr) ) := do
    xT ← infer_type x,
    cs ← induction x,
    gs ← get_goals,
    es ← (list.zip cs gs).mmap (λ c, do
        ⟨⟨n,ls, ss⟩, g⟩ ← pure c,
        set_goals [g],
        e ← resolve_name n >>= pure ∘ pexpr.mk_explicit >>= to_expr,
        T ← infer_type e,
        (ctx,b) ← pure $ telescope.of_pis T,
        args ← pure $ ls.take $ ctx.length,
        indos ← pure $ ls.drop $ ctx.length,
        ⟨[], acc⟩ ← args.mfoldl (λ p a, do
            ⟨indos, acc⟩ ← pure (p : (list expr) × (list ind_arg)),
            T ← infer_type a,
            if expr.get_app_fn xT = expr.get_app_fn T then do
                h::indos ← pure indos,
                pure (indos, ind_arg.recursive a h :: acc) else
            pure (indos, ind_arg.normal a :: acc)
        ) (indos, []),
        acc ← pure $ acc.reverse,
        pure (n, acc, ss)
    ),
    set_goals gs,
    pure es

/-- Automatically derive `has_to_string` for an inductive datatype. -/
@[derive_handler] meta def to_string_handler :=
instance_derive_handler ``has_to_string $
    do
        e ← get_env,
        split,
        x ← intro `x,
        cs ← induction_but_the_recursors_are_kept_with_the_arguments x,
        cs.mmap (λ c, do
            ⟨n,ls,ss⟩ ← pure c,
            constructor_name ← pure $ reflect $ n.components.ilast,
            if ls.empty then refine $ ```(to_string %%constructor_name) else do
            str ← pure $ list.foldl (λ x y, ```(%%x ++ %%y)) ```("") $ list.intersperse ```( " " ) $ list.map (λ x, ```( "(" ++ %%x ++ ")" )) $ ls.map (map_ind_arg (λ x, ```( to_string %%x))),
            refine $ ```(to_string %%constructor_name ++ " " ++ %%str)
        ),
        pure ()

/-- Helper method for has_to_tactic_format_handler -/
private meta def pp_cases : ind_arg → tactic unit
|(ind_arg.normal x) :=
    refine ```(tactic.pp %%x)
    <|> refine ```(pure $ to_fmt %%x)
    <|> refine ```(pure $ format.of_string $ to_string %%x)
    <|> (do
        ppx ← tactic.pp x,
        T ← tactic.infer_type x,
        ppT ← tactic.pp T,
        msg : format ← pure $ to_fmt "Couldn't find a way of showing " ++ ppx ++ " : " ++ ppT,
        tactic.fail $ msg)
|(ind_arg.recursive x r) := refine ```(%%r)

@[derive_handler] meta def has_to_tactic_format_handler :=
instance_derive_handler ``has_to_tactic_format $ do
    split,
    x ← intro `x,
    cs ← induction_but_the_recursors_are_kept_with_the_arguments x,
    cs.mmap (λ x, do
        ⟨n,ls,ss⟩ ← pure x,
        constructor_name ← pure $ reflect $ n.components.ilast,
        cnp ← pure $ ```(tactic.pp %%constructor_name), -- : tactic format
        if ls.empty then refine cnp else do
        pps ← ls.mmap (λ x, do
            g ← mk_meta_var `(tactic format),
            gs ← get_goals,
            set_goals [g],
            pp_cases x,
            set_goals gs,
            instantiate_mvars g),
        ppl ← pure $ pps.foldr (λ x acc, ```(%%x :: %%acc)) ```([]),
        ppl ← pure $ ```(list.mmap id %%ppl), -- : tactic (list format)
        refine ```(pure (λ cnp ppl, cnp ++ (to_fmt "{")++ (format.group $ format.nest 1 $ format.join $ list.intersperse ("," ++ format.line) ppl) ++ "}") <*> %%cnp <*> %%ppl)
    ),
    pure ()

private meta def lt_cases : (ind_arg × ind_arg) → pexpr → pexpr
| (ind_arg.normal a_h, ind_arg.normal b_h) acc :=
    ```((%%a_h < %%b_h) ∨ ((%%a_h = %%b_h) ∧ %%acc))
| (ind_arg.recursive a_h ai, ind_arg.recursive b_h bi) acc :=
    ```((%%ai %%b_h) ∨ ((%%a_h = %%b_h) ∧ %%acc))
| _ acc := acc

/-- Derive a total ordering for a given inductive datatype. This just puts an ordering on the constructor names and then
compares two terms with the same ctor lexically on their arguments. Useful for enabling the datatype to be
stored in rtrees and other structures which require some total ordering on data.
You should only use this if you don't care about the semantics of `<`.
-/
@[derive_handler] meta def lt_derive_handler :=
instance_derive_handler ``has_lt $ do
    split,
    a ← intro `a,
    a_cs ← induction_but_the_recursors_are_kept_with_the_arguments a,
    a_goals ← get_goals,
    (list.zip a_cs a_goals).mmap (λ c, do
        ⟨⟨a_cn,a_hs,a_subs⟩,g⟩ ← pure c,
        b ← intro `b,
        b_cs ← induction_but_the_recursors_are_kept_with_the_arguments b,
        b_goals ← get_goals,
        bz ← pure $ list.zip b_cs b_goals,
        bz.mmap(λ c, do
            ⟨⟨b_cn,b_hs,b_subs⟩,g⟩ ← pure c,
            if a_cn < b_cn then exact `(true) else
            if a_cn > b_cn then exact `(false) else do
            r ← pure $ list.foldr lt_cases ```(false) $ list.zip a_hs b_hs,
            r ← to_expr r,
            exact r
        )
    ),
    set_goals a_goals,
    pure ()

private meta def ltb_cases : (ind_arg × ind_arg) → pexpr → pexpr
| (ind_arg.normal a_h, ind_arg.normal b_h) acc :=
    ```(bor (%%a_h < %%b_h) (band (to_bool $ %%a_h = %%b_h) %%acc))
| (ind_arg.recursive a_h ai, ind_arg.recursive b_h bi) acc :=
    ```(bor (%%ai %%b_h) (band (to_bool $ %%a_h = %%b_h) %%acc))
| _ acc := acc

@[derive_handler] meta def mk_ltb_instance := instance_derive_handler ``has_ltb $ do
    split,
    a ← intro `a,
    (expr.const typename _) ← infer_type a >>= pure ∘ expr.get_app_fn,
    e ← get_env,
    all_cases ← pure $ environment.constructors_of e typename,
    a_cs ← induction_but_the_recursors_are_kept_with_the_arguments a,
    a_goals ← get_goals,
    (list.zip a_cs a_goals).mmap (λ c, do
        ⟨⟨a_cn,a_hs,a_subs⟩,g⟩ ← pure c,
        a_idx ← pure $ list.find_index (= a_cn) all_cases,
        b ← intro `b,
        b_cs ← induction_but_the_recursors_are_kept_with_the_arguments b,
        b_goals ← get_goals,
        bz ← pure $ list.zip b_cs b_goals,
        bz.mmap(λ c, do
            ⟨⟨b_cn,b_hs,b_subs⟩,g⟩ ← pure c,
            b_idx ← pure $ list.find_index (= b_cn) all_cases,
            if a_idx < b_idx then exact `(tt) else
            if a_idx > b_idx then exact `(ff) else do
            r ← pure $ list.foldr ltb_cases ```(ff) $ list.zip a_hs b_hs,
            r ← to_expr r,
            exact r
        )
    ),
    set_goals a_goals,
    pure ()

/-!
# An example:

```
@[derive decidable_eq, derive has_ltb, derive has_to_tactic_format]
inductive qwerty
| nil : qwerty
| asdf (n : nat) : qwerty
| br (x: qwerty) (n : nat) (y : qwerty) : qwerty
| s : qwerty → qwerty

open qwerty
#eval to_bool $  nil < (asdf 3)
#eval to_bool $ s (asdf 3) < s (asdf 4)
#eval to_bool (br (asdf 3) 2 nil < br (asdf 3) 2 nil)
#eval to_bool $ ((asdf 3) < (asdf 4))
run_cmd (trace $ br (asdf 3) 2 nil)
```
-/
end derivations
