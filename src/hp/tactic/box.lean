import basic hp.core

open tactic.unsafe list.zipper combinator

namespace hp

/- The box is the key structure of the humanproof system. See https://edayers.com/thesis/box -/
meta inductive box : Type
| I (h : binder) (b : box)
| V (s : source) (b : box)
| O (bs : list box) -- [todo] each contingent needs to have data for building writeup etc.
| T (h : binder) (b : box)
| A (b1 : box) (h : binder) (b2 : box) -- [note] binder name can be set to some information like case name etc.
| R (r : expr) : box

namespace box

meta def as_R : box → option expr
| (box.R e) := some e
| _ := none

meta def as_T : box → option (binder × box)
| (box.T h b) := some (h,b)
| _ := none

/-- Returns a target with the additional guard that the target is a proposition. -/
meta def as_T_prop : box → type_context (binder × box)
| b := do
  bb@⟨⟨_,bi, y⟩ ,_⟩ ← alternative.returnopt $ as_T b,
  yy ← type_context.infer y,
  ip : bool ← pure $ to_bool $ yy = `(Prop),
  guard ip,
  pure bb

meta def Impossible : box := box.O []

/-- Equality check for a pair of boxes. [todo] decidable equality fails due to nested list in inductive datatype. -/
protected meta def eq : box → box → bool
| (I h1 b1) (I h2 b2) := h1 = h2 ∧ eq b1 b2
| (V s1 b1) (V s2 b2) := s1 = s2 ∧ eq b1 b2
| (O bs1) (O bs2) := list.eq_by eq bs1 bs2
| (A b11 h1 b21) (A b12 h2 b22) := list.all [eq b11 b12, h1 = h2, eq b21 b22] id
| (T x1 b1) (T x2 b2) := x1 = x2 ∧ eq b1 b2
| (R r1) (R r2) := r1 = r2
| _ _ := ff

/-- Apply `f` to each of the expression children of the box. -/
protected meta def mmap_children {m} [monad m] (f : telescope → expr → m expr) : telescope → box → m box
| Γ (I h b) := do h ← (Γ ⍄ f $ h), pure I <*> pure h <*> mmap_children (h::Γ) b
| Γ (V s b) := pure V <*> (Γ ⍄ f $ s) <*> mmap_children Γ b
| Γ (O bs) := pure O <*> (bs.mmap $ mmap_children Γ)
| Γ (T h b) := do
  h ← (Γ ⍄ f $ h),
  b ← mmap_children (h :: Γ) b,
  pure $ T h b
| Γ (A b1 h b2) := do
  b1 ← mmap_children Γ b1,
  h ← (Γ ⍄ f $ h),
  b2 ← mmap_children (h::Γ) b2,
  pure $ A b1 h b2
| Γ (R s) := pure R <*> (Γ ⍄ f $ s)

meta instance : assignable box := ⟨@box.mmap_children⟩

protected meta def pp : box → tactic format
| (I h b) := format.nest_join "I " [tactic.pp h, pp b]
| (V s b) := format.nest_join "V " [tactic.pp s, pp b]
| (O bs) := format.nest_join "O " $ list.map pp bs
| (T h b) := format.nest_join "T " [tactic.pp h, pp b]
| (A b1 h b2) := format.nest_join "A " [pp b1, pure $ "~~~", tactic.pp h, pure $ "~~~", pp b2]
| (R s) := format.nest_join "R " [tactic.pp s]

protected meta def to_fmt : box → format
| (I h b) := format.nest_join_pure "I " [to_string h, to_fmt b]
| (V s b) := format.nest_join_pure "V " [s.to_expr.to_string , to_fmt b]
| (O bs) := format.nest_join_pure "O " $ list.map to_fmt bs
| (T h b) := format.nest_join_pure "T " [to_string h, to_fmt b]
| (A b1 h b2) := format.nest_join_pure "A " [to_fmt b1, "~~~", to_string h, "~~~", to_fmt b2]
| (R s) := format.nest_join_pure "R " [to_string s]


meta instance : has_to_tactic_format box := ⟨box.pp⟩
meta instance : decidable_eq box | b1 b2 := unchecked_cast $ box.eq b1 b2

meta def infer_lambda_body : expr → nat → type_context expr
| e n := do
  y ← type_context.infer e,
  (Γ, r) ← type_context.returnopt $ telescope.of_n_pis e n,
  pure r

/-- Infer the type that this box will return. -/
meta def infer : box → type_context expr
| (I h b) := do
  t ← assignable.with_local h ( λ _, infer ) b,
  pure $ binder.to_pi h t
| (V s b) := b.infer
| (O bs) := list.apick infer bs
| (A b1 h b2) := do
  t ← assignable.with_local h ( λ _, infer ) b2,
  pure t
| (T h b) := do assignable.with_local h (λ _, infer ) b
| (R s) := type_context.infer s

/-- Produce the resulting expression of the box. In the case of mvars a dummy is created. -/
meta def result : box → option expr
| (I h b) := h.to_lam <$> b.result
| (V s b) := b.result
| (O bs) := bs.pick result
| (T h b) := do
  r ← b.result,
  pure $ assignable.instantiate_var r $ binder.to_dummy_mvar h
| (A b1 h b2) := do
  r1 ← b1.result,
  r2 ← result $ assignable.instantiate_var b1 r1,
  pure r2
| (R x) := x

meta def join : box → box → box
| (O []) b := b
| b (O []) := b
| (O bs1) (O bs2) := O $ bs1 ++ bs2
| (O bs1) b := O $ bs1 ++ [b]
| b (O bs2) := O $ [b] ++ bs2
| b1 b2 := O $ [b1] ++ [b2]

/-- If the given box is an `R`, then apply `onDone`, else apply `ow`. -/
meta def map_result (onDone : expr → box) (ow : box → box) : box → box
| (R e) := onDone e
| (O []) := O []
| b := ow b

meta def clean : box → box
| (I h b) := map_result (λ r, R $ h.to_lam r) (I h) $ clean b
| (V s b) := map_result R (V s) $ clean b
| (O bs)  := list.foldl join Impossible $ list.map clean bs
| (T h b) := map_result (λ r, if expr.has_var_idx r 0 then T h b else R $ expr.lower_vars r 1 1) (T h) $ clean b
| (A b1 h b2) :=
  match clean b1 with
  | (O []) := if assignable.has_var_idx b2 0 then O [] else assignable.lower_vars b2 1 1
  | (R r) := clean $ assignable.instantiate_var b2 r
  | b1 := map_result
            (λ r, if expr.has_var_idx r 0 then T h b1 else R $ expr.lower_vars r 1 1)
            (A b1 h)
          $ clean b2
  end
| (R r) := (R r)

meta def Vs : list source → box → box
| (s :: ss) b := box.V s $ Vs ss b
| [] b := b

meta def IV : binder → box → box
| h b := box.I h $ box.V {label := h.name, type := h.type, value := expr.var 0} $ b

meta def with_intro : hyp → box → box
| h b :=
  box.I h.to_binder
  $ box.V {label := h.pretty_name, value := expr.var 0, type := h.type}
  $ assignable.abstract_local b h.uniq_name

meta def with_binder : binder → box → box
| h b := box.I h $ box.V {label := h.name, value := expr.var 0, type := h.type} $ b

meta def with_telescope : telescope → box → box
| (h :: Γ) b := with_telescope Γ $ with_binder h $ b
| [] b := b

meta def dummy_goal := type_context.mk_mvar `dummy_goal `(trivial)

@[derive decidable_eq, derive has_to_tactic_format]
meta inductive coord : Type
| I
| V
| O (idx : nat)
| T
| A1
| A2

meta def coord.follow : coord → box → option box
| coord.I  (I h b)  := some b
| coord.V (V _ b) := some b
| (coord.O idx) (O bs) := list.nth bs idx
| coord.T (T h b) := some b
| coord.A1 (A b _ _) := some b
| coord.A2 (A _ _ b) := some b
| _ _ := none

meta def children : box → list (telescope × coord × box)
| (I h b) := [([h], coord.I, b)]
| (V s b) := [([], coord.V, b)]
| (O bs) := list.map_with_index (λ i b, ([], coord.O i, b)) bs
| (A b1 h b2) :=  [([], coord.A1, b1), ([h], coord.A2, b2)]
| (T h b) := [([h], coord.T, b)]
| (R _) := []

meta def get_coords : box → list coord :=
list.map (prod.fst ∘ prod.snd) ∘ children

meta def address := list coord

meta instance address.httf : has_to_tactic_format (address) := list.has_to_tactic_format

meta def mmap_child_boxes {m} [applicative m] (p : coord → telescope → box → m box) : telescope → box → m box
| Γ (I h b) := pure (I h) <*> p coord.I (h::Γ) b
| Γ (V s b) := pure (V s) <*> p coord.V Γ b
| Γ (O bs) := pure O <*> (list.traverse (λ x, p (coord.O $ prod.fst x) Γ $ prod.snd x) $ list.map_with_index prod.mk $ bs)
| Γ (T h b) := pure (T h) <*> p coord.T (h::Γ) b
| Γ (A b1 h b2) := pure (A) <*> p coord.A1 Γ b1 <*> pure h <*> p coord.A2 (h::Γ) b2
| Γ (R r) := pure (R r)

meta def mfold {m} [monad m] {α} (p : α → list coord → telescope → box → m α) : list coord → telescope → α → box → m α
| radr Γ a b := do
  a ← p a radr Γ b,
  b.children.mfoldl (λ a ⟨Δ,c,b⟩, mfold (c::radr) (Δ ++ Γ) a b) a

meta def fold {α} (p : α → list coord → telescope → box → α) : α → box → α
| a b := @mfold id _ α p [] [] a b

/-- Folds α over the box, if `p` fails, then that branch of the box is skipped. Note the list coord is reversed so it's not an address. -/
meta def afold {m} [monad m] [alternative m] {α} (p : α → list coord → telescope → box → m α) : list coord → telescope → α → box → m α
| radr Γ a b := (do
  a ← p a radr Γ b,
  b.children.mfoldl (λ a ⟨Δ,c,b⟩, afold (c::radr) (Δ ++ Γ) a b) a) <|> pure a

/-- Returns the first a in α for which `p` doesn't fail. -/
meta def mpick {m} [monad m] [alternative m] {α} (p : list coord → telescope → box → m α) : box → m α
| b := do
  (except.error e) ← except_t.run $ @mfold (except_t α m) _ unit (λ _ radr Γ b, do
    o ← monad_lift $ alternative.optreturn $ p radr Γ b,
    match o with | (none) := pure () | (some x) := throw x end
  ) [] [] () b | failure,
  pure e

/-- Take all of the children that don't fail. -/
meta def mcollect {m} [monad m] [alternative m] {α} (p : list coord → telescope → box → m α) : box → m (list α)
| b := list.reverse <$> mfold (λ acc cs Γ b, (pure list.cons <*> p cs Γ b <*> pure acc) <|> (pure acc)) [] [] [] b

meta def find_address {m} [monad m] (p : telescope → box → m bool) : box → m (option address)
|b := option_t.run $ mpick (λ radr Γ b, do
  r ← monad_lift $ p Γ b,
  if r then pure $ radr.reverse else failure) b

meta def find_addresses {m} [monad m] (p : telescope → box → m bool) : box → m (list address)
| b := do
  o ← option_t.run $ mcollect (λ radr Γ b, do
    r ← ⍐ $ p Γ b,
    if r then pure radr.reverse else failure) $ b,
  pure $ [] <| o

meta def target_addresses : box → (list address)
| b := list.reverse $ fold (λ acc radr Γ b, (id <| (as_T b *> (some $ list.cons radr.reverse))) $ acc) [] b

meta def find_source (p : telescope → source → bool) : box → option address
| b := @find_address id _ (λ Γ b,
  match b with
  | (box.V s _) := p Γ s
  | _ := ff
  end
) b

meta def find_with_name (n : name) : box → list address
| t := @find_addresses id _ (λ Γ b,
  match b with
  | (box.T ⟨tn,_,_⟩ _) := tn = n
  | (box.V s _) := s.label = n
  | _ := ff
  end
) t

meta def find_targets_with_name (n : name) : box → list address
| t := @find_addresses id _ (λ Γ b,
  match b with
  | (box.T ⟨tn,_,_⟩ _) := tn = n
  | _ := ff
  end
) t

@[derive_prisms, derive decidable_eq]
meta inductive path : Type
| top (_dummy_goal : expr) -- these can be deleted when we have type_context.set_local_context. The dummy goal is just an mvar that is used to keep the mvar context that the box was created in.
| I (h : hyp) (_dummy_goal : expr) (p : path)
| V (s : source) (p : path)
| O (bs : list.zipper box) (p : path)
| T (s : stub) (p : path)
| A1 (h : binder) (b2 : box) (p : path)
| A2 (b1 : box) (s : stub) (p : path) -- don't bother figuring out declaration of b1, the result of b1 is just an opaque stub.

-- meta inductive path.item : Type
-- | I (h : hyp) (dummy_goal : expr)
-- | V (s : source)
-- | O (bs : list.zipper box)
-- | T (s : stub)
-- | A1 (h : binder) (b2 : box)
-- | A2 (b1 : box) (s : stub)

-- meta structure path2 : Type :=
-- (dummy_goal : expr)
-- (items : list path.item)

namespace path

  protected meta def pp_core : path → tactic (format)
  | (top _) := failure
  | (I h _ p) := format.nest_join "I " [tactic.pp h]
  | (V s p) := format.nest_join "V " [tactic.pp s]
  | (O bs p) := format.nest_join "O " $ list.map tactic.pp $ list.zipper.unzip bs
  | (T s p) := format.nest_join "T " [tactic.pp s]
  | (A1 h b2 p) := format.nest_join "A1 " [tactic.pp h, tactic.pp b2]
  | (A2 b1 s p) := format.nest_join "A2 " [tactic.pp b1, tactic.pp s]

  meta def mmap_children {m} [monad m] (f : telescope → expr → m expr) : telescope → path → m path
  | Γ (path.top dg) := pure path.top <*> (Γ ⍄ f $ dg)
  | Γ (path.I h dg p) := pure path.I <*> (Γ ⍄ f $ h) <*> (Γ ⍄ f $ dg) <*> mmap_children Γ p
  | Γ (path.V s p) := pure path.V <*> (Γ ⍄ f $ s) <*> mmap_children Γ p
  | Γ (path.O bs p) := pure path.O <*> (Γ ⍄ f $ bs) <*> mmap_children Γ p
  | Γ (path.T s p) := pure path.T <*> (Γ ⍄ f $ s) <*> mmap_children Γ p
  | Γ (path.A1 h b2 p) := do
    h ← (Γ ⍄ f $ h),
    b2 ← ((h::Γ) ⍄ f $ b2),
    p ← mmap_children Γ p,
    pure $ path.A1 h b2 p
  | Γ (path.A2 b1 s p) := pure path.A2 <*> (Γ ⍄ f $ b1) <*> (Γ ⍄ f $ s) <*> mmap_children Γ p

  meta instance : assignable path := ⟨@path.mmap_children⟩

  meta def to_address_core : address → path → address
  | acc (path.top _)        := acc
  | acc (path.I h _ p)  := to_address_core (coord.I :: acc) p
  | acc (path.V s p)    := to_address_core (coord.V :: acc) p
  | acc (path.O bs p)   := to_address_core (coord.O bs.depth :: acc) p
  | acc (path.A1 _ _ p) := to_address_core (coord.A1 :: acc) p
  | acc (path.A2 _ _ p) := to_address_core (coord.A2 :: acc) p
  | acc (path.T _ p)    := to_address_core (coord.T :: acc) p

  meta def to_address : path → address := to_address_core []

  meta instance : has_emptyc path := ⟨path.top $ inhabited.default _⟩

  meta def tail : path → option path
  | (top _) := none
  | (I h _ p) := some p
  | (V s p) := some p
  | (O bs p) := some p
  | (A1 _ _ p) := some p
  | (A2 _ _ p) := some p
  | (T _ p) := some p

  meta def list_mmap {m} [applicative m] {α} (f : path → m α) : path → m (list α)
  | p := match tail p with
         | none := pure []
         | (some q) := pure list.cons <*> f p <*> list_mmap q
         end

  protected meta def pp : path → tactic (format) | p := do
    l ← list_mmap path.pp_core p,
    pure $ @list.to_format _ ⟨id⟩ l

  meta instance : has_to_tactic_format path := ⟨path.pp⟩

  meta def length : path → nat
  | p := 0 <| ((+ 1) <$> length <$> tail p)

  meta def dtail : path → path | p := ∅ <| tail p

  meta def mmap_tail {m} [applicative m] (f : path → m path) : path → m path
  | (top dg)   := pure (top dg)
  | (I h dg p) := pure (I h dg) <*> f p
  | (V s p)    := pure (V s)    <*> f p
  | (O bs p)   := pure (O bs)   <*> f p
  | (A1 a b p) := pure (A1 a b) <*> f p
  | (A2 a b p) := pure (A2 a b) <*> f p
  | (T a p)    := pure (T a)    <*> f p

  meta def map_tail : (path → path) → (path → path) := @mmap_tail id _

  meta def foldup {α} (f : path → α → α) : path → α → α
  | p a := match tail p with
           | (some p₂) := foldup p₂ $ f p a
           | none := f p a
           end

  meta def append : path → path → path
  | (top e) p₂ := p₂
  | p₁ p₂ := map_tail (λ p₁, append p₁ p₂) p₁

  meta def intros : path → list hyp
  | p := foldup (λ p l, l <| (λ i, list.cons (prod.fst i) l) <$> as_I p) p []

  meta def source_list : path → list source
  | p := foldup (λ p l, l <| (λ i, list.cons (prod.fst i) l) <$> as_V p) p []

  /-- Go up through the path and get all of the labels of the A1s -/
  meta def A1_list : path → list name
  | p := foldup (λ p l,
    match p with
    | (path.A1 ⟨n,_,_⟩ _ _) := list.cons n l
    | _ := l
    end
  ) p []

  meta def push_I : hyp → path → type_context path
  | h p := do
    dg ← dummy_goal,
    pure $ path.I h dg $ p

  meta def push_IV : hyp → path → type_context path
  | h p := do
    p ← push_I h p,
    pure $ path.V (source.of_hyp h) p

  meta def stubs : path → list stub
  | (path.T s p) := s :: stubs p
  | (path.A2 b1 s p) := s :: stubs p
  | p := [] <| (stubs <$> tail p)

  /-- Returns all of the targets that are declared on this path. -/
  meta def Tstubs : path → list stub
  | (path.T s p) := s :: stubs p
  | p := [] <| (stubs <$> tail p)

  meta def get_dependent_stubs : stub → path → type_context (list stub)
  | s (path.T t p) := do
    tds ← stub.depends_on t s,
    rest ← get_dependent_stubs s p,
    pure $ if tds then t :: rest else rest
  | s (path.A2 b1 t p) := do
    tds ← stub.depends_on t s,
    rest ← get_dependent_stubs s p,
    pure $ if tds then t :: rest else rest
  | s p :=
    match tail p with
    | (some p) := get_dependent_stubs s p
    | (none) := pure []
    end

  meta def push_sources : list source → path → path
  | [] p := p
  | (s :: ss) p := push_sources ss $ path.V s p

  meta def collect_sources : list source → path → list source × path
  | acc (path.V s p) := collect_sources (s :: acc) p
  | acc p := (acc, p)

  /-- Push the sources as high as they can go without breaking dependencies. -/
  meta def push_sources_high : list source → path → path
  | ss (path.I x dg p) := if ss.any (λ s, assignable.has_local_constant x s) then push_sources ss (path.I x dg p) else path.I x dg $ push_sources_high ss p
  | ss q@(path.T x p)  :=
    -- trace "\npsh:" $
    -- trace (x.type.to_string) $
    if ss.any (λ s, assignable.has_mvar x s) then
      push_sources ss q
    else path.T x $ push_sources_high ss p
  | ss (path.top e) := push_sources ss (path.top e)
  | ss q := path.map_tail (push_sources_high ss) q

  -- meta def restrict_O : list.zipper box → path → type_context path
  -- | o (O o₂ p ) := _
  -- | o (top dg) := O o (top dg)
  -- | o (I h dg p) :=

  meta def get_dummy_goal : path → expr
  | (path.I _ dg _) := dg
  | (path.top dg) := dg
  | p := get_dummy_goal $ dtail p

  meta def hoist_source1 : source → path → type_context path
  | s (path.I h dg p) :=
    if h.appears_in s then pure (path.I h dg p) else failure
  | s (path.V s2 p) := pure (path.V s2) <*> hoist_source1 s p
  | s (path.top _) := failure
  | s (path.T t p) :=
    if t.appears_in s then failure
    else (path.T t) <$> (hoist_source1 s p  <|> (pure $ path.V s p))
  | s (path.A2 b t p) :=
    if t.appears_in s then failure
    else (path.A2 b t) <$> (hoist_source1 s p  <|> (pure $ path.V s p))
  | s (path.A1 hb b2 p) := pure (path.A1 hb b2) <*> (hoist_source1 s p <|> (pure $ path.V s p))
  | s (path.O bs p) :=  pure (path.O bs) <*> (hoist_source1 s p <|> (pure $ path.V s p))

  meta def hoist_source : source → path → type_context path
  | s p := do
    s ← assignable.tc.instantiate_mvars s,
    hoist_source1 s p <|> (pure $ path.V s p)

    -- todo if it depends on

  /-- `hoist_target hs s p` finds a place to attach the stub `s` to the path such that `s` is _above_ all of the local_consts in `hs`
  and _above_ all of the mvars in `hs`. So `hs` contains all of the variables and metavariables that depend on `s` and so should be lower in the chain.   -/
  meta def hoist_target : list expr → stub → path → type_context path
  | [] s p :=
    -- trace "adding T" $
    pure $ path.T s p
  | hs s (path.I h dg p) := do
    -- type_context.trace (to_string h.to_expr ++(  list.to_string $ list.map to_string hs )),
    if ¬ hs.any (λ x, x.local_uniq_name = h.uniq_name) then do
      type_context.fail "can't hoist target out of its context."
    else do
      hs ← pure $ hs.filter (λ x, x.local_uniq_name ≠ h.to_expr.local_uniq_name),
      p ← hoist_target hs s p,
      pure $ path.I h dg p
  | hs s (path.T t p) := do
    -- if t is in hs, then t depends on s and s should be hoisted above it.
    -- however, if s depends on t, then there is a cyclic dependency and we should fail.
    sdt ← stub.depends_on s t,
    tds ← stub.depends_on t s,

    if sdt ∧ tds then
      type_context.fail "hoist target: cyclic dependency detected. "
    else do
    -- in the case that sdt is true, we will need to also hoist `t` at some point to get a wf box, but we can do that when we go up on it.
      hs ← pure $ hs.filter (λ x, x.mvar_uniq_name ≠ t.uniq_name),
      p ← hoist_target hs s p,
      pure $ path.T t p
  | hs s (path.top _) :=
    -- trace "hoist_target failed!" $
    failure
  | hs s (path.V sr p) := do
    sr ← assignable.tc.instantiate_mvars sr,
    p ← hoist_target hs s p,
    -- if sr only depends on hs and not any other hs, then hoist it.
    -- [hack] but for now we can just hoist it and it's fine.
    hoist_source sr p
  | hs s p := mmap_tail (hoist_target hs s) p
  -- | hs s (path.O bs p) := -- [todo] need to hoist the O block here...

  -- meta def O_restrict : list.zipper box → path → type_context path
  -- | bs (path.I h dg p) := _

end path

meta def zipper := box.path × box

namespace zipper

  meta def get_path : zipper → path := prod.fst

  meta instance zipper.pp : has_to_tactic_format zipper := prod.has_to_tactic_format _ _
  meta instance asn : assignable zipper := prod.assignable

  meta def down : coord → zipper → type_context zipper
  | coord.I       ⟨p, box.I h b⟩ := do
    h@(expr.local_const un pn bi y) ← h.push_local,
    -- type_context.trace $ ("downI", un,pn ),
    y ← type_context.infer h,
    b ← pure $ assignable.instantiate_var b h,
    p ← path.push_I ⟨un,pn,bi,y⟩ p,
    pure ⟨p, b⟩
  | coord.V       ⟨p, box.V s b⟩ := pure ⟨box.path.V s p, b⟩
  | (coord.O idx) ⟨p, box.O bs⟩ := do
    ⟨b, bz⟩ ← type_context.returnopt $ list.zipper.pinch idx bs,
    pure ⟨box.path.O bz p, b⟩
  | (coord.T) ⟨p, box.T ⟨n, _, y⟩ b⟩:= do
    g ← type_context.mk_mvar n y,
    lctx ← type_context.get_local_context,
    -- type_context.trace $ ("downT", list.to_format $ lctx.to_list.map expr.local_uniq_name),
    gy ← type_context.infer g,
    b ← pure $ assignable.instantiate_var b g,
    pure ⟨path.T ⟨g, gy⟩ p, b⟩
  | (coord.A1) ⟨p, box.A b1 s b2⟩ := do pure ⟨box.path.A1 s b2 p, b1⟩
  | (coord.A2) ⟨p, box.A b1 ⟨n, _, y⟩ b2⟩ := do
    g ← type_context.mk_mvar n y,
    gy ← type_context.infer g,
    b ← pure $ assignable.instantiate_var b2 g,
    pure $ ⟨path.A2 b1 ⟨g,gy⟩ p, b⟩
  | _             _     := failure

  meta def down_all : zipper → list (type_context zipper)
  | z@⟨p,b⟩ := b.get_coords.map (λ c, down c z)

  meta def down_adr : address → zipper → type_context zipper
  | [] z := pure z
  | (c :: rest) z := down c z >>= down_adr rest

  meta def up_impossible : path → type_context zipper
  | (path.top e) := pure $ ⟨(path.top e), box.Impossible⟩
  | (path.I h _ p) := up_impossible p
  | (path.V s p) := up_impossible p
  | (path.O bz p) := if bz.empty then up_impossible p else pure ⟨p, box.O bz.unzip⟩
  | (path.A1 _ _ p) := up_impossible p
  | (path.A2 _ _ p) := up_impossible p
  | (path.T _ p) := up_impossible p

  /-- Take a metavariable `g` and append it to the path.-/
  meta def append_new_mvar_to_path : expr → zipper → type_context zipper
  | g ⟨p, b⟩ := do
    gt ← type_context.infer g,
    gt ← type_context.instantiate_mvars gt,
    s ← pure $ stub.mk g gt,
    -- Γ is the current context
    Γ ← type_context.get_local_context,
    -- Δ is the context that `g` was declared in.
    Δ ← type_context.get_context g,
    -- type_context.trace $ to_fmt Γ,
    -- type_context.trace $ to_fmt Δ,
    -- type_context.trace $ to_fmt $ to_bool $ Γ ≤ Δ,
    if (Γ = Δ) then do
      ds ← path.get_dependent_stubs s p,
      p ← path.hoist_target (ds.map stub.to_expr) s p,
      pure ⟨p, b⟩
    else if (Γ ≤ Δ) then do
      -- take the context difference of the new mvar
      E ← pure $ Δ.to_list \ Γ.to_list,
      -- we need to make a new box for the mvar to live in
      E ← E.mmap hyp.of_expr_tc,
      b1 ← E.mfoldr (λ l b, do
          pure $ box.with_intro l b
        ) $ box.T ⟨expr.mvar_pretty_name g, binder_info.default, gt⟩
        $ box.R $ expr.var 0,
      skolem_type ← b1.infer,
      s ← type_context.mk_mvar g.mvar_pretty_name skolem_type,
      type_context.assign g $ expr.mk_app s $ E.map hyp.to_expr,
      -- [todo] are there cases where the A2 needs to be hoisted?
      -- Usually not because nothing above should depend on `g` because it's not in context.
      -- _however_ in theory yes because you could assign a higher target with a delayed abstraction pointing to this mvar.
      -- For now I'm just going to test that the
      [] ← path.get_dependent_stubs ⟨g,gt⟩ p | type_context.fail "other mvars depend on the abstraction of this mvar, this is not supported currently.",
      pure ⟨path.A2 b1 ⟨s, skolem_type⟩ p, b⟩
    else if (Δ ≤ Γ) then do
      -- metavariable is restricted, so we should push it up the stack.
      -- [todo] an mvar should not pass above an O path element, so the O var should also be restricted.
      E ← pure $ Γ.to_list \ Δ.to_list,
      -- type_context.trace "restricting path context.",
      -- type_context.trace $ to_fmt E,
      -- [todo] add a nice label for the new mvar here.
      ds ← path.get_dependent_stubs s p,
      E ← pure $ E ++ ds.map stub.to_expr,
      p ← path.hoist_target E s p,
      pure ⟨p, b⟩
    else do
      type_context.trace "can only append new mvars that are in the same context",
      type_context.failure

  meta def append_new_mvars_to_path : list expr → zipper → type_context zipper
  | [] z := pure z
  | gs z := do
    -- [todo] may need to sort the gs, some of the g ∈ gs' types might depend on other gs,
    gs.mfoldr append_new_mvar_to_path z

  /- If we make it to here, it means that lean has assigned `e` the mvar `s`, and we need to figure out whether
  there are any new mvars that are not present in the path that need to be added.  -/
  meta def push_assigned : expr → zipper → type_context zipper
  | s₀ z := do
      -- type_context.trace "push_assigned",
      s ← assignable.tc.instantiate_mvars s₀,
      st ← type_context.infer s,
      st ← assignable.tc.instantiate_mvars st,
      z@⟨p,b⟩ ← assignable.tc.instantiate_mvars z,
      -- find the new mvars that this mvar depends on
      deps ← pure $ expr.list_mvars s,
      -- type_context.trace (
      --   to_fmt "assigned var "
      --   ++ (to_fmt $ expr.mvar_pretty_name s₀)
      --   ++ " depends on "
      --   ++ (list.to_format $ list.map expr.mvar_pretty_name $ deps)),
      -- get all of the metavariables that are in scope
      stub_scope ← pure $ list.map stub.to_expr $ path.stubs z.1,
      -- type_context.trace stub_scope,
      -- remove the these from the dependencies.
      new_deps ← pure $ deps \ stub_scope,
      -- add the new mvars to the path
      append_new_mvars_to_path new_deps z

  meta def up_done : list source → path → expr → type_context zipper
  | ss p@(path.top dg) e :=
    pure $ ⟨(path.top dg), box.Vs ss $ box.R e⟩
  | ss (path.I h _ p) e := do
    e ← pure $ expr.abstract_local e h.uniq_name,
    -- type_context.trace ("up_done I", e.to_string),
    e ← pure $ binder.to_lam h.to_binder $ e,
    ss ← pure $ ss.filter (λ s, bnot $ assignable.has_local_constant h.to_expr s),
    up_done ss p e
  | ss (path.V s p) e := do
    up_done (s :: ss) p e
  | ss (path.O bz p) e := do
    -- [todo] might need to perform an O restriction here, not sure.
    up_done ss p e
  | ss (path.A1 s b2 p) e :=
    pure $ ⟨p, box.Vs ss $ assignable.instantiate_var b2 e⟩
  | ss (path.T s p) e := do
    ia ← type_context.is_not_unassigned_mvar s.to_expr,
    ss ← assignable.tc.instantiate_mvars ss,
    if ia then do
      -- type_context.trace $ ( "up_done path.T assigned" ),
      push_assigned s ⟨p , box.Vs ss $ box.R e⟩
    else do
      -- type_context.trace $ "up_done path.T unassigned",
      e ← pure $ assignable.abstract_mvar e $ expr.mvar_uniq_name s,
      ss ← pure $ assignable.abstract_mvar ss $ expr.mvar_uniq_name s,
      -- type_context.trace $ e,
      pure ⟨p, box.T s.to_binder $ box.Vs ss $ box.R $ e⟩
  | ss (path.A2 b1 s p) e := do
    ia ← type_context.is_not_unassigned_mvar s.to_expr,
    p ← pure $ path.push_sources ss.reverse p,
    if ia then
      push_assigned s ⟨p, box.Vs ss $ box.R e⟩
    else do
      ss ← pure $ assignable.abstract_mvar ss $ expr.mvar_uniq_name s,
      pure ⟨p, box.A b1 (binder.of_mvar s) $ box.Vs ss $ box.R $ assignable.abstract_mvar e $ expr.mvar_uniq_name s⟩

  meta def up : zipper → type_context zipper
  | ⟨(path.top _), _⟩ := failure
  | ⟨path.I h _ p, b⟩ := do
    b ← pure $ assignable.abstract_local b h.uniq_name,
    -- type_context.trace ("up I", h.uniq_name, b.to_fmt),
    type_context.pop_local,
    pure ⟨p, box.I h.to_binder b⟩
  | ⟨path.V s p, b⟩ := pure ⟨p, box.V s b⟩
  | ⟨path.O bz p, b⟩ := do
    pure ⟨p, box.O $ list.zipper.unpinch b bz⟩
  | ⟨path.A1 r b2 p, b1⟩ := pure ⟨p, box.A b1 r b2⟩
  | ⟨path.T x p, b⟩ := do
    ia ← type_context.is_not_unassigned_mvar x,
    if ia then do
      -- type_context.trace $ ( "up path.T assigned" ),
      push_assigned x $ prod.mk p b
    else do
      -- type_context.trace $ ( "up path.T unassigned" ),
      -- it is possible that some earlier stub depends on this one, in which case we need to instead hoist this mvar above these other targets.
      pure ⟨p, box.T x.to_binder $ assignable.abstract_mvar b x.uniq_name⟩
  | ⟨path.A2 b1 x p, b2⟩ := do
    ia ← type_context.is_not_unassigned_mvar x,
    if ia then push_assigned x $ prod.mk p b2
    else pure ⟨p, box.A b1 x.to_binder $ assignable.abstract_mvar b2 x.uniq_name⟩

  meta def up_clean : zipper → type_context zipper
  | ⟨path.top _, _⟩ := failure
  | ⟨p, box.O []⟩ := up_impossible p
  | ⟨p, box.R e⟩ := up_done [] p e
  | z := up z

  /-- Returns all of the declared stubs above the cursor. -/
  meta def stubs : zipper → list stub
  | ⟨p, _⟩ := path.stubs p

  /-- Returns all of the declared stubs in T boxes above the cursor. -/
  meta def Tstubs : zipper → list stub
  | ⟨p, _⟩ := path.Tstubs p

  meta instance : decidable_eq zipper := by apply_instance

  meta def left : zipper → type_context zipper
  | ⟨(path.top _), _⟩ := failure
  | z@⟨path.O ⟨[], _⟩ p, b⟩ := failure
  | z@⟨path.O bz p, b⟩ := do
    up z >>= down (coord.O $ bz.depth - 1)
  | z@⟨path.A2 _ _ _, _⟩ := do
    up z >>= down coord.A1
  | z := failure

  meta def right : zipper → type_context zipper
  | ⟨(path.top _), _⟩ := failure
  | z@⟨path.O ⟨_, []⟩ p, b⟩ := failure
  | z@⟨path.O bz p, b⟩ := do
    up z >>= down (coord.O $ bz.depth + 1)
  | z@⟨path.A1 _ _ _, _⟩ := do
    up z >>= down coord.A2
  | z := failure

  meta def top : zipper → type_context zipper
  | z := (up_clean z >>= λ z, top z) <|> pure z

  meta def unzip : zipper → type_context box
  | z := prod.snd <$> top z

  meta def zip : box → type_context zipper
  | b := do
    dg ← dummy_goal,
    pure ⟨(path.top dg), b⟩

  meta def down_O : zipper → list (type_context zipper)
  | z@⟨p, O bs⟩ := bs.map_with_index (λ i _, down (coord.O i) z)
  | _ := []

  meta def set_ctx : zipper → tactic unit | z := tactic.set_goals $ [z.1.get_dummy_goal]

  meta def goto (n : name) : zipper → type_context zipper
  | z@⟨p,b⟩ :=
    (match b with
    | (box.V s b) := if s.label = n then pure z else failure
    | (box.T s b) := if s.name = n then pure z else failure
    | _ := failure
    end)
    <|>
    (list.apick (>>= goto) $ down_all z)

end zipper

meta def all_targets : box → type_context (expr × list expr)
| b@(I hb x) := do
  ⟨path.I h _ p, b⟩ ← zipper.down coord.I $ ⟨∅, b⟩,
  (res, targs) ← all_targets b,
  type_context.pop_local,
  pure (hb.to_lam $ expr.mk_delayed_abstraction res [h.uniq_name], targs)
| (V s b) := all_targets b
| b@(T s x) := do
  ⟨path.T s p, b⟩ ← zipper.down coord.T $ ⟨∅, b⟩,
  (r, targs) ← all_targets b,
  pure $ (r, s :: targs)
| b@(A b1 h b2) := do
  (r1, ts1) ← all_targets b1,
  (r2, ts2) ← all_targets $ assignable.instantiate_var b2 r1,
  pure (r2, ts1 ++ ts2)
| b@(O []) := failure
| (O (b :: rest)) := all_targets b -- todo for now just take the first possibility to prevent cluttering.
| (R e) := pure (e, [])

/-- Monad for zippers. -/
meta def Z := state_t zipper type_context

namespace Z

  section
    local attribute [reducible] Z
    meta instance : monad Z := by apply_instance
    meta instance : monad_state zipper Z := by apply_instance
    meta instance : alternative Z := by apply_instance
    meta instance : has_monad_lift type_context Z := ⟨λ α x, monad_lift x⟩
    meta instance tactic_hp_coe {α : Type} : has_coe (type_context α) (Z α) := ⟨monad_lift⟩
  end

  meta def returnopt {α} : option α → Z α := monad_lift ∘ type_context.returnopt
  meta def fail {α} : format → Z α := monad_lift ∘ type_context.fail

  meta def of_ztz : (zipper → type_context zipper) → Z unit
  | f := ⟨λ z, prod.mk () <$> f z⟩

  meta def down : coord → Z unit := Z.of_ztz ∘ zipper.down
  meta def up : Z unit := Z.of_ztz zipper.up
  meta def up_clean : Z unit := Z.of_ztz zipper.up_clean
  meta def down_adr : address → Z unit := Z.of_ztz ∘ zipper.down_adr
  meta def goto := down_adr

  meta def cursor : Z box := prod.snd <$> get
  meta def set_cursor (b : box) : Z unit := modify $ prod.map id $ K b
  meta def modify_cursor (f : box → box) : Z unit := modify $ prod.map id f
  meta def coords : Z (list coord) := get_coords <$> cursor

  meta def down_first : Z unit := do
    (c :: _) ← coords,
    down c

  meta def down_last : Z unit := do
    l ← coords,
    c ← returnopt $ list.olast l,
    down c

  meta def left : Z unit := of_ztz zipper.left
  meta def right : Z unit := of_ztz zipper.right

  private meta def fix_ru : Z unit :=
  right <|> (do up, fix_ru)

  private meta def fix_down_last : Z unit :=
  (do down_last, fix_down_last) <|> (pure ())

  meta def next : Z unit :=
  down_first <|> fix_ru

  meta def previous : Z unit :=
  (do left, fix_down_last) <|> up

  meta def top : Z unit :=
  (do up, top) <|> pure ()

  meta def source_list : Z (list source)  := do
    ⟨p, _⟩ ← get,
    ls ← pure $ box.path.source_list p,
    pure ls

  meta def push_source : source → Z unit
  | s := modify (prod.map (path.V s) id)

  meta def push_sources_high : list source → Z unit
  | ss := do
    ⟨p,b⟩ ← get,
    put $ ⟨path.push_sources_high ss p, b⟩

  meta def down_stub : Z stub := do
    down coord.T,
    ⟨path.T g p, b⟩ ← get,
    pure g

  meta def first_goal : Z unit := do
    b ← cursor,
    some adr ← box.find_address (λ Γ b, pure $ option.is_some $ b.as_T) b,
    down_adr adr
  meta def first_prop_goal : Z unit := do
    b ← cursor,
    some adr ← ⍐ $ box.find_address (λ Γ b, alternative.is_ok b.as_T_prop) b,
    down_adr adr

  meta def prop_goal_addresses : Z (list address) := do
    b ← cursor,
    adrs ← ⍐ $ box.find_addresses (λ Γ b, alternative.is_ok b.as_T_prop) b,
    pure adrs

  meta def get_dummy_goal_for_pp : Z expr := do
    ⟨p,_⟩ ← get,
    pure $ path.get_dummy_goal p

  meta def down_I : Z hyp := do
    down coord.I,
    ⟨path.I h _ _, _⟩ ← get,
    pure h

  meta def down_V : Z source := do
    down coord.V,
    ⟨path.V s _, _⟩ ← get,
    pure s

  meta def down_IV : Z hyp := do
    down coord.I,
    ⟨path.I h _ _, _⟩ ← get,
    down coord.V,
    ⟨path.V _ _, _⟩ ← get,
    pure h

  meta def repeat {α} : Z α → Z (list α)
  | z := (do a ← z, list.cons a <$> repeat z) <|> pure []

  meta def down_context : Z (list hyp × list source × expr) := do
  (hs, vs) ← list.partition_sum <$> repeat (sum.inl <$> down_I <|> sum.inr <$> down_V),
  g ← get_dummy_goal_for_pp,
  pure (hs, vs, g)

  /-- Gets the deepest target. -/
  meta def goto_last_target : Z unit := do
    cs ← coords,
    match cs.olast with
    | (none) := up *> pure ()
    | (some c) := down c *> goto_last_target
    end

  meta def goto_name : name → Z unit
  | n := Z.of_ztz $ zipper.goto n

  /-- takes some unregistered targets and pushes them on to the zipper.
  [warn] make sure that they really are unregistered! -/
  meta def register_targets : list stub → Z unit
  | xs := Z.of_ztz $ (zipper.append_new_mvars_to_path $ xs.map stub.to_expr)

  section
    variables {m : Type → Type} [monad m] [monad_state box m] [alternative m] [has_monad_lift tactic m]
    /-- `run_tactic zz t` runs the zipper monad `zz`, runs the tactic `t` and then unzips. -/
    meta def run_tactic {α β} :
      (Z β) → (β → m α) → m α
    | zz t := do
      bx ← get,
      -- ① run the `zz : Z β` to create the mvar context and `b : β`.
      (goals, z, dg, b) ← monad_lift $ type_context.run $ (do
        z ← zipper.zip bx,
        (b, z) ← state_t.run zz z,
        -- set the goals that the tactic sees to be all of the declared targets.
        goals ← pure $ z.Tstubs,
        dg ← pure $ z.1.get_dummy_goal, -- used so that we can access the current local_context later,
        pure (goals, z, dg, b)
      ),
      -- ② push the original set of goals
      ogs ← monad_lift $ tactic.get_goals,
      monad_lift $ tactic.set_goals $ list.map stub.to_expr goals,
      -- ③ run the tactic
      a ← t b,
      -- ④ set the dummy goal so that the context is right for the unzipping.
      monad_lift $ tactic.set_goals [dg],
      new_box ← monad_lift $ type_context.run $ (do
        bx ← zipper.unzip z,
        pure bx
        -- [todo] add a sanity check that bx doesn't depend on any mvars
      ),
      -- ⑤ pop back the original goals
      monad_lift $ tactic.set_goals ogs,
      -- ⑥ set the new box state.
      put new_box,
      pure a

    meta def run {α} : Z α → m α
    | zz := do
      run_tactic zz pure

-- [todo] move this to waterfall.
    meta def split : (Z unit) → m unit -- [todo] multi-split things.
    | zz := do
      run_tactic (zz *> down_stub) (λ s, do
        monad_lift $ tactic.set_goals [s],
        monad_lift $ tactic.split,
        pure ()
      )
    /-- Assuming the cursor is a a T, this replaces that target with a new box, if there are other boxes after the target
    then these will be wrapped in an `A` box, or otherwise it will just be a straight replacement. -/
    meta def replace_current_target : box → Z unit | b := do
      box.T s rest ← cursor,
      match rest with
      | (box.R (expr.var 0)) := set_cursor b
      | rest := do
        set_cursor $ box.A b s rest,
        down coord.A1
      end
  end

open tactic

end Z

/-- assume that we just have one mvar right at the start.-/
meta def init : list expr → expr  → tactic box
| Γ e@(expr.mvar un pn _) :=do
  y ← tactic.infer_type e,
  hyps ← list.mmap hyp.of_expr Γ,
  p ← pure $ hyps.foldl (λ p l, path.V (source.of_hyp l) p) (path.top e),
  b ← type_context.run $ (do zipper.unzip $ ⟨path.T ⟨expr.mvar un `T y, y⟩ p, box.R e⟩),
  pure $ b
| _ _ := tactic.fail "need to init with an mvar"

end box

end hp