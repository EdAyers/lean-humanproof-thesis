import order.bounded_lattice .list

universe u

/-- A Hesse diagram but remove edges until its a tree. -/
inductive poset_tree (α β: Type u)
| mk : α → list β → list poset_tree → poset_tree
open poset_tree
namespace poset_tree
variables {α β : Type u} [has_lt α] [decidable_rel ((<) : α → α → Prop)] [decidable_eq α]

mutual def inserts, insert

with inserts : (α × β) → list (poset_tree α β) → list (poset_tree α β)
| (a, b) [] := [mk a [b] []]
| (a, b) (h :: t) :=
  match insert (a, b) h with
  | none := h :: (inserts (a, b) t)
  | (some h) := h :: t
  end

with insert : (α × β) → poset_tree α β → option (poset_tree α β)
| (a, b) (mk x bs h) := if a < x then mk a [b] [mk x bs h]
                else if a > x then mk x bs $ inserts (a, b) h
                else if a = x then mk x (b :: bs) h
                else none

def of_list : list (α × β) → list (poset_tree α β) := list.foldr inserts []

variables [has_bot α]

def insert' : (α × β) → poset_tree α β → poset_tree α β
| (a,b) t :=
  match insert (a,b) t with
  | none := mk ⊥ [] [mk a [b] [t]]
  | (some t) := t
  end

instance : has_emptyc (poset_tree α β) := ⟨mk ⊥ [] []⟩
instance : has_insert (α × β) (poset_tree α β) := ⟨insert'⟩

def of_list' : list (α × β) → poset_tree α β := list.foldr insert' ∅

-- [todo] make unmeta
meta def find_subtree (p : α → bool) : poset_tree α β → option (poset_tree α β)
| t@(poset_tree.mk a bs rest) :=
  if p a then some t else
  list.pick find_subtree rest

end poset_tree