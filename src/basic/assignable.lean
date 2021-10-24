import .list_zipper .telescope .control .list

private meta def run_inside_lambda (f : expr → expr) : telescope → expr → expr
| [] e := f e
| ((binder.mk n bi y) :: rest) e := expr.lambda_body $ run_inside_lambda rest $ expr.lam n bi y e

/- A type α is assignable when you can run a monad over it with expressions. -/
meta class assignable (α : Type) :=
(mmap_children {t : Type → Type} [monad t] (f : telescope → expr → t expr) : telescope → α → t α)

namespace assignable

open assignable
variables {α : Type} [assignable α]

meta def get_children : α → list (telescope × expr)
| a :=
  prod.fst
    $ writer_m.run
    $ @mmap_children α _ (writer_m (list _)) _ (λ bs e, writer_m.tell [(bs, e)] *> pure e) [] a

meta def fold_children {β} (f : β → telescope → expr → β) : β → α → β
| b a := list.foldl (λ b p, f b (prod.fst p) (prod.snd p)) b $ get_children a

meta def map_children (f : telescope → expr → expr) (a : α) : α :=
@mmap_children α _ id _ f [] a

meta def instantiate_mvars : α → tactic α :=
mmap_children (λ bs e, tactic.instantiate_mvars e) []

meta def tc.instantiate_mvars : α → tactic.unsafe.type_context α :=
mmap_children (λ bs e, tactic.unsafe.type_context.instantiate_mvars e) []

meta def lower_vars : α → nat → nat → α
| a s d := map_children (λ bs e, expr.lower_vars e (s + bs.length) d) a

meta def lift_vars : α → nat → nat → α
| a s d := map_children (λ bs e, expr.lift_vars e (s + bs.length) d) a

meta def get_free_var_range : α → nat
| a := list.foldl max 0  $ list.map (list.length ∘ prod.fst)  $ get_children a

meta def has (p : telescope × expr → Prop) [decidable_pred p] : α → bool
| a := list.foldl bor ff $ list.map (λ q, to_bool $ p q) $ get_children a

meta def has_var : α → bool :=
has (λ p, expr.get_free_var_range p.2 > p.1.length)

meta def has_var_idx : α → nat → bool
| a n := has (λ p, expr.has_var_idx p.2 (n + p.1)) a

meta def has_local : α → bool :=
has (λ p, expr.has_local p.2)

meta def has_meta_var : α → bool :=
has (λ p, expr.has_meta_var p.2)

meta def abstract_local : α → name → α
| a n := map_children (run_inside_lambda (λ e, expr.abstract_local e n)) a

meta def abstract_locals : α → list name → α
| a n := map_children (run_inside_lambda (λ e, expr.abstract_locals e n)) a

meta def abstract_mvar : α → name → α
| a n := map_children (λ Γ x, expr.abstract_mvar Γ.length x n) a

meta def instantiate_nth : nat → α → expr → α
| n a r :=
  if get_free_var_range a ≤ n then a else
  map_children (λ t x,
      let fvr := expr.get_free_var_range x in
      if expr.get_free_var_range x ≤ t.length + n then x else
      expr.instantiate_nth_var (t.length + n) x (expr.lift_vars r (t.length) 0)
    ) a

meta def instantiate_vars : α → list expr → α
| a xs := map_children (λ t e, expr.instantiate_vars_core e t.length xs) a

meta def instantiate_var : α → expr → α
| a x := instantiate_vars a [x]

meta def instantiate_locals (s : list (name × expr)) (e : α) : α :=
instantiate_vars (abstract_locals e (list.reverse (list.map prod.fst s))) (list.map prod.snd s)

meta def replace (a : α) (f : expr → nat → option expr) : α :=
map_children (λ t e, expr.replace e $ λ e n, f e $ n + t.length) a

notation Γ` ⍄ `f := assignable.mmap_children f Γ

variables {β : Type} [assignable β]
open tactic.unsafe

/- attach the binder b to the context, perform the function, then pop and abstract the local. -/
meta def with_local (b : binder) : (expr → α → type_context β) → (α → type_context β)
| f a := do
  h ← binder.push_local b,
  b ← f h $ assignable.instantiate_var a h,
  type_context.pop_local,
  pure $ assignable.abstract_local b $ expr.local_uniq_name h

meta def has_local_constant : expr → α → bool
| x := has (λ p, expr.has_local_constant p.2 x)

meta def has_mvar : expr → α → bool
| x := has (λ p, expr.has_meta_var x && expr.has_mvar p.2 x)

end assignable

meta instance expr.assignable : assignable expr :=
{mmap_children := λ t _ f Γ e, f Γ e }

meta def assignable_of_traversable {t : Type → Type} [traversable t] {α : Type} [assignable α] : assignable (t α) :=
⟨λ m mt f Γ ta, begin unfreezingI {refine traverse (assignable.mmap_children f Γ) ta} end⟩

meta instance list.assignable {α : Type} [assignable α] : assignable (list α) :=
{mmap_children := λ t mt f Γ l, @list.mmap t mt _ _ (@assignable.mmap_children _ _ t mt f Γ) l}

meta instance list.zipper.assignable {α : Type} [assignable α] : assignable (list.zipper α) := assignable_of_traversable

meta instance prod.assignable {α β : Type} [assignable α] [assignable β] : assignable (α × β) :=
{mmap_children := λ t [mt:monad t] f Γ l,
  begin unfreezingI {
      exact pure prod.mk <*> assignable.mmap_children f Γ l.1 <*> assignable.mmap_children f Γ l.2,
} end}

meta def binder.mmap_children {t : Type → Type} [monad t] (f : telescope → expr → t expr) : telescope → binder → t binder
| Γ ⟨n, bi, y⟩ := pure (binder.mk n bi) <*> f Γ y

meta def cotelescope.mmap_children {t : Type → Type} [monad t] (f : telescope → expr → t expr) : telescope → cotelescope → t cotelescope
| Γ [] := pure []
| Γ (b :: tail) := do
  b ← binder.mmap_children f Γ b,
  pure (list.cons b) <*> cotelescope.mmap_children (b::Γ) tail

meta def telescope.mmap_children  {t : Type → Type} [monad t] (f : telescope → expr → t expr) : telescope → telescope → t telescope
| Γ bs := list.reverse <$> (cotelescope.mmap_children f Γ $ bs.reverse)

meta instance binder.assignable : assignable binder := ⟨@binder.mmap_children⟩

meta instance telescope.assignable : assignable (telescope) :=
{mmap_children := @telescope.mmap_children}

meta instance cotelescope.assignable : assignable (cotelescope) :=
{mmap_children := @cotelescope.mmap_children}

meta def cotelescope.to_telescope : cotelescope → telescope := list.reverse

meta def telescope.to_metas : telescope → tactic (list expr)
| c := do
    c.mfoldr (λ ⟨n, bi, y⟩ acc, do
      m ← tactic.mk_meta_var (expr.instantiate_vars y acc),
      pure $ m :: acc
    ) []

meta instance telescope.pp : has_to_tactic_format telescope :=
⟨λ x, format.join <$> list.intersperse " " <$> list.mmap tactic.pp x.reverse⟩
/-- Makes an app such that `telescope.of_pis (telescope.mk_app t x) t` η-reduces to `x`  -/
meta def telescope.mk_app : telescope → expr → expr
| t e := expr.mk_app e $ list.reverse $ t.map_with_index (λ i _, expr.var i)

meta def cotelescope.mk_locals_core : cotelescope → list expr → local_context → option (list expr × local_context)
| [] acc lc := pure (acc, lc)
| (⟨n,bi,y⟩ :: t) acc lc := do
  y ← pure $ expr.instantiate_vars y acc,
  (l, lc) ← local_context.mk_local n y bi lc,
  cotelescope.mk_locals_core t (l::acc) lc

meta def telescope.mk_locals : telescope → local_context → option (list expr × local_context)
| t lc := cotelescope.mk_locals_core t.reverse [] lc

open expr

meta def expr.traverse_with_depth {m : Type → Type} [applicative m]
(f : telescope → expr → m (expr)) :
  telescope → expr → m (expr)
 | Γ (var v)  := pure $ var v
 | Γ (sort l) := pure $ sort l
 | Γ (const n ls) := pure $ const n ls
 | Γ (mvar n n' e) := mvar n n' <$> f Γ e
 | Γ (local_const n n' bi e) := local_const n n' bi <$> f Γ e
 | Γ (app e₀ e₁) := app <$> f Γ e₀ <*> f Γ e₁
 | Γ (lam n bi e₀ e₁) := lam n bi <$> f Γ e₀ <*> f (⟨n, bi,e₀⟩::Γ) e₁
 | Γ (pi n bi e₀ e₁) := pi n bi <$> f Γ e₀ <*> f (⟨n,bi,e₀⟩::Γ) e₁
 | Γ (elet n e₀ e₁ e₂) := elet n <$> f Γ e₀ <*> f Γ e₁ <*> f (⟨n,binder_info.default, e₀⟩ :: Γ) e₂
 | Γ (macro mac es) := macro mac <$> list.traverse (f Γ) es


open tactic.unsafe

namespace assignable

/-- Abstracts each subexpression that passes `test`. If `test` fails then that subexpression is not traversed. -/
meta def abstract_this_expr_core (test : expr → type_context bool) : telescope → expr → type_context expr
| Γ e := (do
  r ← test e,
  if r then pure $ expr.var Γ.length else
  match e with
  | (expr.var i) := if i ≥ Γ.length then pure (expr.var (i+1)) else pure (expr.var i)
  | e := expr.traverse_with_depth abstract_this_expr_core Γ e
  end)
  <|> (pure $ expr.lift_vars e Γ.length 1)

/-- [warning] this will give malformed expressions if the starting expr contains free vars. -/
meta def abstract_these_expr_core (test : expr → type_context bool) : telescope → expr → state_t (list (binder × expr)) type_context expr
| Γ e := do
  bms ← get,
  r ← monad_lift $ test e,
  if ¬ r then do
    expr.traverse_with_depth abstract_these_expr_core Γ e
  else do
    y ← monad_lift $ type_context.infer e,
    bm ← pure $ (binder.mk `a binder_info.default y, e),
    bms ← pure $ list.insert bm bms,
    put bms,
    match list.bfind_index (= bm) bms with
    | (some i) := pure (expr.var $ (bms.length - i - 1) + Γ.length)
    | none := failure
    end

variables {α : Type} [assignable α]

meta def abstract_these_core (test : expr → type_context bool) : telescope → α → state_t (list (binder × expr)) type_context α
| Γ a := assignable.mmap_children (abstract_these_expr_core test) Γ a

meta def abstract_these (test : expr → type_context bool) : α → type_context (telescope × α × list expr)
| e := do
  (e, bms) ← state_t.run (abstract_these_core test [] e) [],
  (Γ, xs) ← pure $ list.unzip bms,
  pure (Γ, e, xs)

meta def abstract_this (test : expr → type_context bool) : α → type_context (α)
| a := mmap_children (abstract_this_expr_core test) [] a

meta def kabstract (e : α) (t : expr) (md := reducible) (unify := tt) : tactic α :=
mmap_children (λ Γ c, tactic.kabstract c t md unify) [] e

meta def depends_on : α → expr → bool
| a e@(expr.mvar _ _ _) := has_mvar e a
| a e@(expr.local_const _ _ _ _) := has_local_constant e a
| a e := ff

end assignable


-- run_cmd  (do
--   (Γ, e, rest) ← type_context.run $ assignable.abstract_these (λ e, pure $ e = `(1) ∨ e = `(0)) (`(0 + 1 + (λ x, 1 + x) 4 + 0) : expr),
--   tactic.trace e,
--   e ← pure $ Γ.to_lams e,
--   tactic.trace rest,
--   x ← tactic.head_beta $ expr.mk_app e rest,
--   tactic.trace $ x,

--   pure ()
-- )
