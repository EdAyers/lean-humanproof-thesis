import .table .tactic .telescope .assignable

universes u

/-- The key of an expression is the 'head symbol' of the given expression. -/
meta def expr_table.get_key {elab :bool} : expr elab → name
|(expr.app (expr.mvar _ _ _) _) := `expr_table.app
|(expr.app (expr.var _) _) := `expr_table.app
|(expr.app (expr.local_const _ _ _ _) _) := `expr_table.app
|(expr.app f a) := expr_table.get_key f
|(expr.const n _) := n
|(expr.var n) := `expr_table.wildcard
|(expr.sort _) := `expr_table.sort
|(expr.lam _ _ _ b) := expr_table.get_key b
|(expr.pi _ _ _ b) := expr_table.get_key b
|(expr.macro _ _) := `expr_table.macro
|(expr.local_const _ _ _ _) := `lc
|(expr.mvar _ _ _) := `mv
-- |(expr.var _) := `v
|(expr.elet _ _ _ b) := expr_table.get_key b
-- |e := `expr_table.default

meta structure pattern_table.entry (α : Type) :=
(key : name)
(pattern : pexpr)
(result : list expr → tactic α)

meta def pattern_table (α : Type) := listdict name (_root_.pattern_table.entry α)

namespace pattern_table

variables {α β : Type}

meta instance entry_pp : has_to_tactic_format (entry α) :=
⟨λ x, tactic.pp $ entry.pattern x⟩

meta instance : has_to_tactic_format (pattern_table α) := listdict.has_pp
-- meta def to_pattern_core' : expr → tactic (expr × list level × list expr)
-- | (lam n bi d b) := do
--    id         ← mk_fresh_name,

--    let x     := local_const id n bi d,
--    let new_b := instantiate_var b x,
--    (p, xs) ← to_pattern_core new_b,
--    return (p, x::xs)
-- | e              := return (e, [])

-- /-- Given a pre-term of the form `λ x₁ ... xₙ, t[x₁, ..., xₙ]`, converts it
--    into the pattern `t[?x₁, ..., ?xₙ]` with outputs `[?x₁, ..., ?xₙ]` -/
-- meta def pexpr_to_pattern (p : pexpr) : tactic pattern :=
-- do /- Remark: in the following to_expr, we allow metavars but we do *not* create new goals for them.
--       mk_pattern will convert them into temporary metavars. -/
--    e ← to_expr p tt ff,
--    (new_p, xs) ← to_pattern_core e,
--    mk_pattern [] xs new_p [] xs

/-- See tactic.pexpr_to_pattern. -/
meta def entry.of_pexpr : pexpr → (list expr → tactic α) → tactic (entry α)
| p f := do
  k ← tactic.hypothetically $ expr_table.get_key <$> tactic.to_expr p, -- just to check that it works.
  pure ⟨k,p,f⟩


meta def empty : pattern_table α := listdict.empty
meta instance : has_emptyc (pattern_table α) := ⟨empty⟩

meta def insert : entry α → pattern_table α → (pattern_table α)
| e pt := listdict.insert e.key e pt
meta instance : has_insert (entry α) (pattern_table α) := ⟨insert⟩

protected meta def entry.map (f : α → β) : entry α → entry β
| ⟨k,p,r⟩ := ⟨k,p, r >=> pure ∘ f⟩

protected meta def map (f : α → β) (p : pattern_table α) :=
listdict.map (entry.map f) p

meta def entry.match: expr → entry α → tactic α
| e ⟨k,p,f⟩ := tactic.hypothetically $ do
    -- tactic.trace "entry.match",
    -- tactic.trace_state,
    -- tactic.local_context >>= tactic.trace,
    b ← tactic.trace_fail $ tactic.to_expr p,
    (bs, b) ← pure $ telescope.of_lams b,
    -- tactic.trace (b),
    ms ← telescope.to_metas bs,
    b ← pure $ expr.instantiate_vars b ms,
    match b, e with
    | (expr.app bf@(expr.mvar _ _ _) ba), (expr.app ef ea) := do
      tactic.unify bf ef, -- [todo] break out in to method `unify_but_not_stupid_for_apps`
      tactic.unify ba ea
    | b, e := do
      tactic.unify b e
    end,
    -- tactic.trace "entry.match found a match:",
    -- tactic.trace b,
    all_assigned ← list.mmap (tactic.is_assigned) ms,
    ms ← list.mmap tactic.instantiate_mvars ms,
    f $ ms.reverse

meta def get : pattern_table α → expr → tactic (list α)
| pt e := do
  e ← tactic.instantiate_mvars e,
  k ← pure $ expr_table.get_key e,
  -- tactic.trace ("pattern_table.get ", e,  k.to_string),
  -- [todo] wildcard case
  ls ← pure $ listdict.get k pt,
  -- tactic.trace ls,
  ls : list α ← ls.achoose (entry.match e),
  pure ls

meta def of_list : list (entry α) → pattern_table α
| l := list.foldr insert ∅ l

meta instance pt_has_append : has_append (pattern_table α ) :=
show has_append (listdict _ _), by apply_instance

end pattern_table
