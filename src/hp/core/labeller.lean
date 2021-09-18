import basic hp.core.source

/- System for assigning labels to things that is not as bad as the built in one. -/

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

meta instance : has_mem name labeller := ⟨λ n l, n ∈ l.in_play⟩
meta instance {n} {l : labeller} : decidable (n ∈ l) := by apply_instance

/- [todo] user attribute that allows users to add their own  -/

meta def default_labels := ["x", "y", "z", "v", "w", "a", "b", "c"]

meta def default_class_pool : listdict string string :=
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
            , ("→", ["f", "g", "h"])
            , ("sequence" , ["κ", "σ", "τ"])
            , ("set", ["A", "B", "C", "D", "E", "X", "Y", "Z", "U", "V", "W", "P", "Q", "R", "S", "T"])
            , ("fin", ["i", "j", "k", "r", "s", "t"])
            , ("nat", ["n", "m", "p", "q", "i", "j", "r", "t"])
            , ("hom", ["f", "g", "h", "k", "l", "q", "r", "s", "t", "u", "v", "w"])
            -- , ("real", ["x", "y", "z"])
            , ("real", ["ε", "δ", "η", "ζ", "θ", "α", "β", "γ", "ω"])
            , ("Type", ["α", "β", "γ", "δ", "ε"])
            , ("Prop", ["P", "Q", "R"])
]

meta instance : inhabited labeller :=
⟨{ in_play := ∅
, counts := dictd.empty (λ _, 0)
, cp := default_class_pool
, tp := default_type_pool
, ep := default_element_pool
}⟩

meta def to_subscript_digit : nat → string
| 0 := "₀" | 1 := "₁" | 2 := "₂" | 3 := "₃" | 4 := "₄" | 5 := "₅" | 6 := "₆" | 7 := "₇" | 8 := "₈" | 9 := "₉"
| n := "♘"

meta def to_digits_rev : nat → list nat
| 0 := []
| n := (n % 10) :: to_digits_rev (n / 10)

meta def to_subscript : nat → string
| 0 := "₀"
| n := string.join $ list.map to_subscript_digit $ list.reverse $ to_digits_rev $ n

/- Here are the rules for looking up potential label names for a given expression (x : α).
- if `α = f ..xs`, look up `f.last` in `type_pool`
- if `α = Type`, look up "Type" in `type_pool`
- if `α = Prop`, look up "Prop" in `type_pool`
- if `α = expr.pi _ _ _ _`, look up "→" in `type_pool`,
- if `[C α]` for some class `C`, look up `C` in `element_pool`.
- if `[C x]` for some class `C`, look up `C` in `class_pool`.
  Also note that `[C x]` might not be in context yet, so might need to be clever with when labelling occurs.

 -/

variables {m : Type → Type} [monad m] [monad_state labeller m] [has_monad_lift tactic m] {α β : Type}

meta def get_fn_name : expr → string
| (expr.app f _) := get_fn_name f
| (expr.pi _ _ _ _) := "→"
| (expr.sort level.zero) := "Prop"
| (expr.sort _) := "Type"
| (expr.const n _) := n.last
| _ := "none"

meta def is_in_play : name → m bool | n:= do
  labs ← get,
  pure $ n ∈ in_play labs

meta def push_label : name → m unit | n := do
  modify $ labeller.modify_in_play $ insert n

meta def select_label : list string → m name
| [] := ⍐ $ tactic.fail "need to select from at least one label"
| ss := do
  labs ← get,
  unused ← pure $ ss.find ((∉ labs) ∘ mk_simple_name),
  -- ⍐ $ tactic.trace unused,
  match unused with
  | (some h) := do
    n ← pure $ mk_simple_name h,
    push_label n,
    pure n
  | none := do
    ss ← pure $ ss.map (λ x, (x, labs.counts.get x)),
    some (base, i) ← pure $ ss.min_by (int.of_nat ∘ prod.snd),
    n ← pure $ mk_simple_name $ base ++ to_subscript i,
    -- ⍐ $ tactic.trace (base, i),
    modify $ labeller.modify_counts $ λ cs, cs.modify (+ 1) base,
    push_label n,

    pure n
  end

meta def label_intro (is_src : bool) : binder → cotelescope → m name
| ⟨n,bi,y⟩ rest := do
  y ← ⍐ $ tactic.instantiate_mvars $ y,
  labs ← get,
  ip ← ⍐ $ tactic.is_prop y,
  if ip then do
    -- if it's a Prop, then make it an H or a T.
    base ← pure $ if is_src then "H" else "T",
    select_label [base]
  else if n ≠ name.anonymous ∧ n ∉ labs then do
    -- if the binder name is not anon and is not in the labeller
    -- then register it as a label and return it.
    push_label n,
    pure n
  else do
    -- instantiate the rest of the cotelescope with a local.
    rest ← pure $ assignable.instantiate_var rest $ expr.local_const n n bi y,

    cls ← pure $ rest.collect $ λ b,
      match b with
      | ⟨_, binder_info.inst_implicit, expr.app (expr.const f _) (expr.local_const un _ _ _)⟩ :=
        if un = n then labs.cp.get f.last else []
      | _ := []
      end,
    -- cs are the typeclasses that the type belongs to
    cs ← ⍐ $ tactic.get_classes y,

    els ← pure $ cs.collect $ λ c, labs.ep.get c.last,
    -- ⍐ $ tactic.trace $ get_fn_name y,
    tls ← pure $ labs.tp.get $ get_fn_name y,
    ns ← pure $ cls ++ els ++ tls,
    ns ← pure $ if ns.empty then default_labels else ns,
    -- ⍐ $ tactic.trace $ ("selecting from names: ", ns),
    select_label ns

meta def label (p: pool) : expr → tactic (list string)
| T := do
  cs ← tactic.get_classes T,
  ts : string ← pure $ match expr.app_fn T with
        | (expr.const f _) := f.head
        | (expr.pi _ _ _ _) := "→"
        | _ := "none"
        end,
  ls ← pure $ cs.collect $ λ c, p.get c.head,
  pure $ match ls with
        | [] := p.get ""
        | ls := ls
        end


-- meta def get_fresh_label (ls : labeller) (type : string) (parent : name) : id (labeller × name) := do
--   -- [todo] also check the local_context.
--   if ¬(name.is_private parent ∨ parent = name.anonymous ∨ table.contains parent ls.in_play) then pure (ls, parent) else do
--   base ← pure $ match parent with
--   | name.anonymous := ""
--   | name.mk_numeral i n := ""
--   | name.mk_string  s n := s
--   end,
--   pool ← pure $ ls.pools.get base,
--   pool ← pure $ if pool.empty then ls.pools.get "" else pool,

--   ls ← pure $ { labeller .
--     in_play := ls.in_play.insert n,
--     counts := ls.counts.modify (+ 1) base,
--     ..ls
--   },
--   pure (ls, n)

open tactic.unsafe

meta def rename_meta : expr → m expr
| m@(expr.mvar un pn _):= do
  -- ⍐ tactic.trace_state,
  y ← ⍐ $ tactic.infer_type m >>= tactic.instantiate_mvars,
  b ← pure $ binder.mk name.anonymous binder_info.default y,
  label ← label_intro ff b [],
  -- ⍐ $ tactic.trace ("rename_meta", un, y, label),
  -- [todo] check if pn is sensible or something like `_mvar_.....`
  ⍐ $ type_context.run $ do
    -- pure (ls, mvar)
    lctx ← type_context.get_context m,
    g ← type_context.mk_mvar label y lctx,
    type_context.assign m g,
    pure g
| _ := ⍐ $ tactic.fail "not an mvar"

meta def type_to_label_type_key : expr → tactic string
| e := pure $ expr.to_string e -- [todo]

-- meta def rename_meta (ls : labeller) (mvar : expr) (parent : name := name.anonymous) : tactic (labeller × expr) := do
--   y ← tactic.infer_type mvar,
--   ip ← tactic.is_prop y,
--   if ip then rename_meta_core ls "target" parent mvar else do
--   type ← type_to_label_type_key y,
--   rename_meta_core ls type parent mvar

-- meta def get_fresh_binder_label (ls : labeller) : binder → tactic (labeller × binder)
-- | ⟨n,bi,y⟩ := do
--   ys ← type_to_label_type_key y,
--   (ls, n) ← pure $ get_fresh_label ls ys n,
--   pure (ls, ⟨n,bi,y⟩)

meta def label_cotelescope : cotelescope → m cotelescope
| [] := pure []
| (b :: rest) := do
  n ← label_intro tt b rest,
  -- ⍐ $ tactic.trace ("relabel", b, n),
  b ← pure $ {name := n, ..b},
  l ← ⍐ $ binder.mk_local b,
  rest ← pure $ @assignable.instantiate_var cotelescope (cotelescope.assignable) rest l,
  -- ⍐ $ tactic.trace (rest.reverse),
  rest ← label_cotelescope (rest),
  rest ← pure $ assignable.abstract_local rest l.local_uniq_name,
  -- ⍐ $ tactic.trace (rest.reverse),
  pure $ b :: rest

meta def label_telescope : telescope → m telescope :=
(pure ∘ list.reverse) >=> label_cotelescope >=> (pure ∘ list.reverse)

meta def free_label  (n : name) : m unit := do
  ls ← get,
  put $ ls.modify_in_play (dict.erase n),
  pure ()

meta def relabel_source : source → m source
| src := do
  l ← label_intro tt ⟨src.label, binder_info.default, src.type⟩ [],
  pure {label := l, ..src}


end labeller

end hp