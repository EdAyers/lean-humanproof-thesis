import .list .list_zipper
universes u v

/-- Core inductive datatype for ltree.
This is morally the same as `|mk : α → list (ltree α) → ltree α` but note that
having a recursive argument with lists causes a funky mutual inductive compiler definition
that I wanted to avoid for simplicity. -/
@[derive decidable_eq]
inductive ltree.core (α : Type u) : bool → Type u
| nil  : ltree.core ff
| cons : ltree.core tt → ltree.core ff → ltree.core ff
| mk (a : α) (children : ltree.core ff) : ltree.core tt

/-- A list tree where each node has an item α and a list of child trees. Compare with the binary tree in data.tree.
This is equivalent to the inductive definition `| mk : α → list (ltree α) → ltree α`.
-/
def ltree (α : Type u) := ltree.core α tt

namespace ltree

local attribute [reducible] ltree
open ltree.core
variables {α β : Type u}

def head_item : ltree α → α
| (mk a _) := a

def map_head_item (f : α → α) : ltree α → ltree α
| (mk a c) := mk (f a) c

def set_head_item (a : α) : ltree α → ltree α :=
map_head_item (λ _, a)

meta def core.of_list_unsafe : list (ltree α) → ltree.core α ff := unchecked_cast

meta def core.to_list_unsafe : ltree.core α ff → list (ltree α) := unchecked_cast

@[vm_override core.of_list_unsafe]
def core.of_list : list (ltree α) → ltree.core α ff
| [] := ltree.core.nil
| (x :: rest) := ltree.core.cons x $ core.of_list rest

@[vm_override core.to_list_unsafe]
def core.to_list : ltree.core α ff → list (ltree α)
| ltree.core.nil := []
| (ltree.core.cons x rest) := list.cons x $ core.to_list rest

def mk : α → list (ltree α) → ltree α
| a cs := ltree.core.mk a $ core.of_list cs

def decons : ltree α → α × list (ltree α)
| (core.mk a c) := (a, core.to_list c)

def leaf : α → ltree α
| a := ltree.mk a []

def core.map (f : α → β) : Π {b}, ltree.core α b → ltree.core β b
| _ (core.mk a c) := core.mk (f a) $ core.map c
| _ (core.nil) := core.nil
| _ (core.cons x rest) := core.cons (core.map x) (core.map rest)

protected def map (f : α → β) : ltree α → ltree β := core.map f

instance : has_pure ltree :=
⟨λ α, leaf⟩

instance : functor ltree :=
{map := @ltree.map}

def children : ltree α → list (ltree α) :=
prod.snd ∘ decons

def set_children : list (ltree α) → ltree α → ltree α
| c t := mk (head_item t) c

def core.traverse {m : Type u → Type v} [applicative m] {α β} (f: α → m β): Π {b}, ltree.core α b → m (ltree.core β b)
| _ (core.mk a cs) := pure core.mk <*> f a <*> core.traverse cs
| _ (core.nil) := pure $ core.nil
| _ (core.cons t cs) := pure core.cons <*> core.traverse t <*> core.traverse cs


instance : traversable ltree :=
⟨λ m 𝒜 α β f x, @core.traverse m 𝒜 α β f tt x⟩

def fold {β} (f : β → α → β) : β → ltree α → β
| b t := traversable.foldl f b t

def to_list : ltree α → list α :=
fold (λ t h, h :: t) []

def is_leaf : ltree α → bool :=
list.empty ∘ children

def get_leaves_aux : Π {b}, list α → ltree.core α b → list α
| _ acc (core.mk a $ core.nil) := a :: acc
| _ acc (core.mk _ $ c) := get_leaves_aux acc c
| _ acc (core.nil) := acc
| _ acc (core.cons t cs) := get_leaves_aux (get_leaves_aux acc t) cs

def get_leaves : ltree α → list α := get_leaves_aux []

meta def pp [has_to_tactic_format α] : ltree α → tactic format
| t := pure (λ a cs, a ++ "[" ++ (format.nest 2 $ format.join $ list.intersperse ("," ++ format.line) $ cs) ++ "]") <*> tactic.pp t.head_item <*> list.mmap pp t.children

meta instance [has_to_tactic_format α] : has_to_tactic_format (ltree α) := ⟨pp⟩

meta def mprune {T} [monad T] [alternative T] (f : α → T β) : ltree α → T (ltree β)
| t := f t.head_item >>= λ b, mk b <$> list.achoose mprune t.children

meta def prune (p : α → bool) : ltree α → option (ltree α) :=
mprune (λ x, if p x then some x else none)

private def core.stringify (s : α → string) : Π {b}, ltree.core α b → string
| _ (core.mk a cs) := "ltree.mk (" ++ s a ++ ") [" ++ core.stringify cs
| _ (core.cons t core.nil) := core.stringify t ++ "]"
| _ (core.cons t cs) := core.stringify t ++ ", " ++ core.stringify cs
| _ (core.nil) := "]"

instance [has_repr α] : has_repr (ltree α) := ⟨λ t, core.stringify repr t⟩
instance [has_to_string α] : has_to_string (ltree α) := ⟨λ t, core.stringify to_string t⟩

@[derive decidable_eq]
inductive zipper.path (α : Type u)
|top : zipper.path
|down : α → list.zipper (ltree α) → zipper.path → zipper.path

/-- A zipper on ltrees. -/
@[derive decidable_eq]
structure zipper (α : Type u) :=
(p : zipper.path α)
(cursor : ltree α)

namespace zipper

def path.fold (f : β → α → list.zipper (ltree α) → β) : β → path α → β
| b (path.top) := b
| b (path.down a l p) := path.fold (f b a l) p

def path.items : path α → list α
|(path.top) := []
|(path.down a _ p) := a :: path.items p

def zip : ltree α → zipper α
| t := ⟨path.top, t⟩

def up : zipper α → option (zipper α)
|⟨path.top, c⟩ := none
|⟨path.down a l p,c⟩ := some $ zipper.mk p $ ltree.mk a $ list.zipper.unpinch c l

def idx : zipper α → option ℕ
|⟨path.top, _⟩ := none
|⟨path.down _ z _, _⟩ := some z.depth

def up_with_index : zipper α → option ((zipper α) × ℕ)
| z := option.bind (idx z) $ λ i, option.bind (up z) $ λ z, some (z,i)

/-- Go up and remove the current mk from the resulting ltree. -/
def up_drop : zipper α → option (zipper α)
|⟨path.top, c⟩ := none
|⟨path.down a l p, c⟩ := some $ zipper.mk p $ ltree.mk a $ list.zipper.unzip l

private def top_aux : path α → ltree α → zipper α
|(path.top) c := ⟨path.top, c⟩
|(path.down a l p) c := top_aux p $ ltree.mk a $ list.zipper.unpinch c l

def top : zipper α → zipper α
| ⟨p,c⟩ := top_aux p c

def unzip : zipper α → ltree α := cursor ∘ top

def down : ℕ → zipper α → option (zipper α)
|n ⟨p,t⟩ := do
  (a,z) ← list.zipper.pinch n t.children,
  pure $ zipper.mk (path.down t.head_item z p) a

/- Return a list of all possible child zippers. -/
def down_all : zipper α → list (zipper α)
|⟨p, t⟩ :=
  list.map (λ z, zipper.mk (path.down t.head_item (prod.snd z) p) z.1)
  $ list.zipper.pinch_all t.children

/-- Go down on all children whose index is strictly less than the given `i`. -/
def down_all_lt (i : ℕ) : zipper α → list (zipper α) :=
list.take i ∘ down_all

/-- Check that the cursor is a leaf. -/
def is_leaf : zipper α → bool
| ⟨p, t⟩ := ltree.is_leaf t

/-- Alias for down_all -/
def children : zipper α → list (zipper α) := down_all

def set_cursor : ltree α → zipper α → zipper α
| t ⟨p,_⟩ := ⟨p,t⟩

def map_cursor : (ltree α → ltree α) → zipper α → zipper α
| f z := set_cursor (f $ cursor z) z

def set_children : list (ltree α) → zipper α → zipper α
| c z := map_cursor (ltree.set_children c) z

/--Replace the children of cursor to be leaves of the given list instead.-/
def grow : list α → zipper α → zipper α
| c z := z.map_cursor $ ltree.set_children $ leaf <$> c

/-- Get the item at the cursor. -/
def item : zipper α → α :=
head_item ∘ cursor

def map_item (f : α → α) : zipper α → zipper α :=
map_cursor (map_head_item f)

def set_item : α → zipper α → zipper α
| a := map_cursor (set_head_item a)

variables {M : Type u → Type v} [monad M]

def core.mfold_down {m : Type u → Type v} [monad m] {α β} (f: β → zipper α → m β): Π {b}, β → path α → ltree.core α b → m β
| _ b p t@(core.mk a cs) := do b ← f b ⟨p,t⟩, core.mfold_down b (path.down a ⟨[], core.to_list cs⟩ p) cs
| _ b p (core.nil) := pure b
| _ b (path.down a ⟨l,j::r⟩ p) (core.cons t cs) := do
  b ← core.mfold_down b (path.down a ⟨l,r⟩ p) t,
  core.mfold_down b (path.down a ⟨j::l, r⟩ p) cs
| _ b (path.down _ _ _) (core.cons _ _) := pure b
| _ b (path.top) (core.cons _ _) := pure b

def mfold_down (f : β → zipper α → M β) : β → zipper α → M β
| b ⟨p,t⟩ := core.mfold_down f b p t

def fold_down (f : β → zipper α → β) : β → zipper α → β :=
@mfold_down _ _ id _ f

def get_leaves : zipper α → list (zipper α)
| z := fold_down (λ b z, if is_leaf z then z :: b else b) [] z

def mfold_up_core (f : β → zipper α → M β) : β → path α → ltree α → M β
| b (path.top) t := f b ⟨path.top, t⟩
| b p0@(path.down a z p) t := do
  b ← f b ⟨p0, t⟩,
  mfold_up_core b p (ltree.mk a $ z.unpinch t)

def mfold_up (f : β → zipper α → M β) : β → zipper α → M β
| b ⟨p,t⟩ := mfold_up_core f b p t

def fold_up (f : β → zipper α → β) : β → zipper α → β
| b z := @mfold_up _ _ id _ f b z

/-- Get all of the items in the ltree that are _strictly above_ the cursor position. -/
def strict_above : zipper α → list α := path.items ∘ zipper.p

/-- Get all of the items in the ltree that are _above or at_ the cursor position. -/
def lax_above : zipper α → list α :=
λ z, z.item :: (path.items $ zipper.p $ z)

def depth : zipper α → ℕ :=
list.length ∘ strict_above

def any_strict_above {α} (f : α → bool) : zipper α → bool :=
λ z, z.strict_above.any f

meta def pp_item_with_indent [has_to_tactic_format α] : zipper α → tactic format := λ z, do
  pa ← tactic.pp z.item,
  n ← pure $ z.depth,
  pure $ (format.join $ list.repeat " " n) ++ pa

meta def get_non_failures {T} [monad T] [alternative T] {β} (f : zipper α → T β) : zipper α → T (list β)
|z := (singleton <$> f z) <|> (list.mcollect get_non_failures $ down_all z)

end zipper

section widget
  open widget

  meta def view {α γ} (vv : component α γ) : ltree α →  (list (html γ))
  | t := [html.of_component t.head_item vv, h "ul" [] $ t.children.reverse.map $ λ c, h "li" [] $ view c]

end widget

end ltree