import basic hp.core.source

/-! System for assigning labels to things.
Labels are chosen from hard-coded sets of letters.
Which set is used depends on the type of the thing being labelled.
So for example a group element should be labelled with `g`, `h` etc
but a point in a metric space should be labelled with `x`, `y` etc.

[todo] Allow adding new suggested name lists with attributes.
[todo] I think that a lot of non-humanproof tactics would benefit (in terms of user-friendliness) from
using this kind of labelling system. Perhaps there is some way it can be integrated with Lean.

# Labelling pools

A labelling pool is a dictionary `string β list string` sending a key string to a set of possible labels.
A labeller is defined by three pools:
- Class pool: sending names of classes `π` to labels for types `Ξ±` that are instances of `π`.
  For example a type `_ : Type` implementing `group _` should be labelled `G`.
  If a class has multiple arguments, the first argument is always bound to.
- Element pool: Suppose we have `Ξ± : Type` and `[π Ξ±]` for some typeclass `π`, then the element pool contains labels for the elements of `Ξ±`.
  For example, `{G : Type} [group G]` causes `_ : G` to be labelled `g` or `h`. While `[metric_space X]` will be labelled `x y : X`
- Type pool: takes the function constant name of a type as the key and returns element names for that type.
  Eg terms of type `set Ξ±` will be labelled `A`, `B` etc.

-/
namespace hp

meta def labeller.pool := listdict string string

@[derive_setters]
meta structure labeller :=
-- class pool
(cp : labeller.pool)
-- element pool
(ep : labeller.pool)
-- type pool
(tp : labeller.pool)
(in_play : table name)
(counts : dictd string nat)

namespace labeller

meta instance : has_mem name labeller := β¨Ξ» n l, n β l.in_playβ©
meta instance {n} {l : labeller} : decidable (n β l) := by apply_instance

/- [todo] user attribute that allows users to add their own  -/

meta def default_labels := ["x", "y", "z", "v", "w", "a", "b", "c"]

meta def default_class_pool : pool :=
listdict.of [
  ("category", ["C", "D", "E"]),
  ("group", ["G", "H"]),
  -- ("point", ["x", "y", "z", "v", "w", "a", "b", "c"]),
  ("has_mem", ["a", "b", "c", "x", "y", "z", "u", "v", "w", "p", "q", "r", "s", "t"]),
  ("metric_space" , ["X", "Y", "Z"])
]

meta def default_element_pool : pool :=
listdict.of [ ("category", ["X","Y","Z"])
            , ("group", ["g", "h", "a", "b", "c", "x", "y", "z"]) ]

/-- pool for converting the head const of the type of an expression to its label -/
meta def default_type_pool : pool :=
listdict.of [ ("", ["x", "y", "z", "a", "b", "c"]) -- default
            , ("β", ["f", "g", "h"])
            , ("sequence" , ["ΞΊ", "Ο", "Ο"])
            , ("set", ["A", "B", "C", "D", "E", "X", "Y", "Z", "U", "V", "W", "P", "Q", "R", "S", "T"])
            , ("fin", ["i", "j", "k", "r", "s", "t"])
            , ("nat", ["n", "m", "p", "q", "i", "j", "r", "t"])
            , ("hom", ["f", "g", "h", "k", "l", "q", "r", "s", "t", "u", "v", "w"])
            -- , ("real", ["x", "y", "z"])
            , ("real", ["Ξ΅", "Ξ΄", "Ξ·", "ΞΆ", "ΞΈ", "Ξ±", "Ξ²", "Ξ³", "Ο"])
            , ("Type", ["Ξ±", "Ξ²", "Ξ³", "Ξ΄", "Ξ΅"])
            , ("Prop", ["P", "Q", "R"])
]

meta instance : inhabited labeller :=
β¨{ in_play := β
, counts := dictd.empty (Ξ» _, 0)
, cp := default_class_pool
, tp := default_type_pool
, ep := default_element_pool
}β©

meta def to_subscript_digit : nat β string
| 0 := "β" | 1 := "β" | 2 := "β" | 3 := "β" | 4 := "β" | 5 := "β" | 6 := "β" | 7 := "β" | 8 := "β" | 9 := "β"
| n := "β"

meta def to_digits_rev : nat β list nat
| 0 := []
| n := (n % 10) :: to_digits_rev (n / 10)

meta def to_subscript : nat β string
| 0 := "β"
| n := string.join $ list.map to_subscript_digit $ list.reverse $ to_digits_rev $ n

/- Here are the rules for looking up potential label names for a given expression (x : Ξ±).
- if `Ξ± = f ..xs`, look up `f.last` in `type_pool`
- if `Ξ± = Type`, look up "Type" in `type_pool`
- if `Ξ± = Prop`, look up "Prop" in `type_pool`
- if `Ξ± = expr.pi _ _ _ _`, look up "β" in `type_pool`,
- if `[C Ξ±]` for some class `C`, look up `C` in `element_pool`.
- if `[C x]` for some class `C`, look up `C` in `class_pool`.
  Also note that `[C x]` might not be in context yet, so might need to be clever with when labelling occurs.

 -/

variables {m : Type β Type} [monad m] [monad_state labeller m] [has_monad_lift tactic m] {Ξ± Ξ² : Type}

meta def get_fn_name : expr β string
| (expr.app f _) := get_fn_name f
| (expr.pi _ _ _ _) := "β"
| (expr.sort level.zero) := "Prop"
| (expr.sort _) := "Type"
| (expr.const n _) := n.last
| _ := "none"

meta def is_in_play : name β m bool | n:= do
  labs β get,
  pure $ n β in_play labs

meta def push_label : name β m unit | n := do
  modify $ labeller.modify_in_play $ insert n

meta def trace_label_state : m unit := do
  labs β get,
  trace (to_string $ labs.in_play) (pure ()),
  pure ()

meta def select_label : list string β m name
| [] := β $ tactic.fail "need to select from at least one label"
| ss := do
  labs β get,

  unused β pure $ ss.find ((β labs) β mk_simple_name),
  match unused with
  | (some h) := do
    n β pure $ mk_simple_name h,
    push_label n,
    pure n
  | none := do
    ss β pure $ ss.map (Ξ» x, (x, labs.counts.get x)),
    some (base, i) β pure $ ss.min_by (int.of_nat β prod.snd),
    n β pure $ mk_simple_name $ base ++ to_subscript i,
    modify $ labeller.modify_counts $ Ξ» cs, cs.modify (+ 1) base,
    push_label n,
    pure n
  end

meta def label_intro (is_src : bool) : binder β cotelescope β m name
| β¨n,bi,yβ© rest := do
  y β β $ tactic.instantiate_mvars $ y,
  labs β get,
  ip β β $ tactic.is_prop y,
  if ip then do
    -- if it's a Prop, then make it an H or a T.
    base β pure $ if is_src then "H" else "T",
    select_label [base]
  else if n β  name.anonymous β§ n β labs then do
    -- if the binder name is not anon and is not in the labeller
    -- then register it as a label and return it.
    push_label n,
    pure n
  else do
    -- instantiate the rest of the cotelescope with a local.
    rest β pure $ assignable.instantiate_var rest $ expr.local_const n n bi y,

    cls β pure $ rest.collect $ Ξ» b,
      match b with
      | β¨_, binder_info.inst_implicit, expr.app (expr.const f _) (expr.local_const un _ _ _)β© :=
        if un = n then labs.cp.get f.last else []
      | _ := []
      end,
    -- cs are the typeclasses that the type belongs to
    cs β β $ tactic.get_classes y,

    els β pure $ cs.collect $ Ξ» c, labs.ep.get c.last,
    -- β $ tactic.trace $ get_fn_name y,
    tls β pure $ labs.tp.get $ get_fn_name y,
    ns β pure $ cls ++ els ++ tls,
    ns β pure $ if ns.empty then default_labels else ns,
    -- β $ tactic.trace $ ("selecting from names: ", ns),
    select_label ns

meta def label (p: pool) : expr β tactic (list string)
| T := do
  cs β tactic.get_classes T,
  ts : string β pure $ match expr.app_fn T with
        | (expr.const f _) := f.head
        | (expr.pi _ _ _ _) := "β"
        | _ := "none"
        end,
  ls β pure $ cs.collect $ Ξ» c, p.get c.head,
  pure $ match ls with
        | [] := p.get ""
        | ls := ls
        end


-- meta def get_fresh_label (ls : labeller) (type : string) (parent : name) : id (labeller Γ name) := do
--   -- [todo] also check the local_context.
--   if Β¬(name.is_private parent β¨ parent = name.anonymous β¨ table.contains parent ls.in_play) then pure (ls, parent) else do
--   base β pure $ match parent with
--   | name.anonymous := ""
--   | name.mk_numeral i n := ""
--   | name.mk_string  s n := s
--   end,
--   pool β pure $ ls.pools.get base,
--   pool β pure $ if pool.empty then ls.pools.get "" else pool,

--   ls β pure $ { labeller .
--     in_play := ls.in_play.insert n,
--     counts := ls.counts.modify (+ 1) base,
--     ..ls
--   },
--   pure (ls, n)

open tactic.unsafe

meta def rename_meta : expr β m expr
| m@(expr.mvar un pn _):= do
  -- β tactic.trace_state,
  y β β $ tactic.infer_type m >>= tactic.instantiate_mvars,
  b β pure $ binder.mk name.anonymous binder_info.default y,
  label β label_intro ff b [],
  -- β $ tactic.trace ("rename_meta", un, y, label),
  -- [todo] check if pn is sensible or something like `_mvar_.....`
  β $ type_context.run $ do
    -- pure (ls, mvar)
    lctx β type_context.get_context m,
    g β type_context.mk_mvar label y lctx,
    type_context.assign m g,
    pure g
| _ := β $ tactic.fail "not an mvar"

meta def type_to_label_type_key : expr β tactic string
| e := pure $ expr.to_string e -- [todo]

-- meta def rename_meta (ls : labeller) (mvar : expr) (parent : name := name.anonymous) : tactic (labeller Γ expr) := do
--   y β tactic.infer_type mvar,
--   ip β tactic.is_prop y,
--   if ip then rename_meta_core ls "target" parent mvar else do
--   type β type_to_label_type_key y,
--   rename_meta_core ls type parent mvar

-- meta def get_fresh_binder_label (ls : labeller) : binder β tactic (labeller Γ binder)
-- | β¨n,bi,yβ© := do
--   ys β type_to_label_type_key y,
--   (ls, n) β pure $ get_fresh_label ls ys n,
--   pure (ls, β¨n,bi,yβ©)

meta def label_cotelescope : cotelescope β m cotelescope
| [] := pure []
| (b :: rest) := do
  n β label_intro tt b rest,
  -- β $ tactic.trace ("relabel", b, n),
  b β pure $ {name := n, ..b},
  l β β $ binder.mk_local b,
  rest β pure $ @assignable.instantiate_var cotelescope (cotelescope.assignable) rest l,
  -- β $ tactic.trace (rest.reverse),
  rest β label_cotelescope (rest),
  rest β pure $ assignable.abstract_local rest l.local_uniq_name,
  -- β $ tactic.trace (rest.reverse),
  pure $ b :: rest

meta def label_telescope : telescope β m telescope :=
(pure β list.reverse) >=> label_cotelescope >=> (pure β list.reverse)

meta def free_label  (n : name) : m unit := do
  ls β get,
  -- put $ ls.modify_in_play (dict.erase n),
  pure ()

meta def relabel_source : source β m source
| src := do
  l β label_intro tt β¨src.label, binder_info.default, src.typeβ© [],
  pure {label := l, ..src}


end labeller

end hp