/- This file contains an adjacency-list implementation of a directed graph.
   However, I've chosen the definitions a bit wierdly to make my use case for this easier.
   Each vertex has an object called an 'edge collection' which contains the information about
   the outgoing edges from the vertex. The idea of separating it this way is that
   one can attach data to the edge collections and also equality checking is only done on the vertices, not the edge cols.
   So the type of vertices should have a quick equality checking algorithm on them.
 -/
import basic.table

section defs
    variables (V : Type) [has_lt V] [decidable_rel ((<) : V → V → Prop)]
    variable (E : Type)

    /-- implementing edge_col allows it to be used as an adjacency table for the graph.
        This is generalised from table because the user may wish to add additional data to the edges.
    -/
    class edge_col :=
    (children : E → list V)
    (push_child : V → E → E)
    (empty {} : E)

    meta structure digraph [edge_col V E] :=
    (edges : dict V E)
    (parents : dict V (table V)) -- reverse lookup calculated automatically from `edges`.
end defs

namespace digraph
/-- Tree representation of a digraph. -/
inductive tree (X : Type)
|crossref : X → tree
|mk : X → list tree → tree

namespace tree
  variable {X : Type}
  variable [has_to_tactic_format X]
  meta def pp : tree X → tactic format
  |(tree.mk x t) := do
      x ← tactic.pp x,
      t ← list.mmap pp t,
      pure $ x ++ "[" ++ (list.foldl (++) "" $ list.reverse $ list.intersperse ", " $ t)  ++ "]"
  |(tree.crossref x) := do
      x ← tactic.pp x,
      pure $ "⟨" ++ x ++ "⟩"
  meta instance : has_to_tactic_format (tree X) := ⟨pp⟩
end tree

section GGG

parameters {V : Type} [has_lt V] [decidable_rel ((<) : V → V → Prop)] {E : Type} [edge_col V E]

local notation `G` := digraph V E

meta def children (e : E) : list V :=
edge_col.children e

protected meta def empty : G :=
{ edges := ∅
, parents := ∅
}

meta instance : has_emptyc G := ⟨empty⟩

meta def get_parents (v : V) (g : G) : table V :=
option.get_or_else (g.parents.get v) ∅

-- meta def table_of_list_list : list (list V) → table V :=
-- list.foldl (λ t l, list.foldl (λ t v, table.insert v t) t l) ∅
meta def get_children (v : V) (g : G) : list V :=
option.get_or_else (children <$> g.edges.get v) []

meta def get_edge (v : V) (g : G) : option E := g.edges.get v

meta def get_edge_or_empty (v : V) (g : G) : E :=
option.get_or_else (g.edges.get v) (edge_col.empty V)

meta def set (v : V) (e : E) (g : G) : G :=
    let prev_children := table.from_list $ get_children v g in
    let new_children := table.from_list $ children e in
    let add_these := new_children \ prev_children in
    let remove_these := prev_children \ new_children in
    let parents := g.parents in
    let parents := table.fold (λ ps r, dict.modify_when_present (λ t, table.erase v t) r ps) parents remove_these in
    let parents := table.fold (λ ps a, dict.modify (λ t, table.insert v $ option.get_or_else t ∅) a ps) parents add_these in
    { edges := dict.insert v e g.edges
    , parents := parents
    }

meta def map_edge (f : E → E) (v : V) (g : G) : G := set v (f (get_edge_or_empty v g)) g

meta def append_child : V → V → G → G
| parent child g := digraph.set parent (edge_col.push_child child $ option.get_or_else (g.edges.get parent) (edge_col.empty V)) g

meta def append_children : V → list V → G → G
| parent children g := list.foldl (λ g child, append_child parent child g) g children

meta def contains : V → G → bool
| v g := g.parents.contains v || g.edges.contains v

meta instance : has_mem V G := ⟨λ v g, contains v g⟩

meta instance {v : V} {g : G} : decidable (v ∈ g) := by apply_instance

/-- Breadth-first folding over a front. -/
meta def fold_aux {T} [monad T] [alternative T] {β} (f : V → option E → β → T β) (g : G)
    : Π (front : list V) (visited : table V), β → T β
| [] visited acc := pure acc
| (h::t) visited acc := do
    e ← pure $ g.edges.get h,
    cs ← pure $ list.bfilter (∉ visited) $ option.get_or_else (children <$> e) [],
    ((f h e acc) >>= fold_aux (t ++ cs) (visited.insert h)) <|> pure acc

meta def fold {T} [monad T] [alternative T] {β} (f : V → option E → β → T β) (g : G) (v₀ : V) (b : β) : T β := fold_aux f g [v₀] ∅ b

meta def traverse_aux {T} [monad T] {β : Type} (get_next : V → (list V)) (f : V → T (β ⊕ (list β → T β)))
    : Π (visited : dict V (option β)), V → T (dict V (option β))
| visited h :=
    match (dict.get h visited) with
    |(some (some b)) := pure visited
    |(some (none)) := undefined_core "graph loop detected"
    |none := do
        r₁ ← f h,
        match r₁ with
        |(sum.inl b) := pure $ dict.insert h (some b) $ visited
        |(sum.inr z) := do
            cs ← pure $ get_next h,
            visited ← pure $ dict.insert h none visited,
            visited ← cs.mfoldl traverse_aux visited,
            bs ← pure $ list.filter_map (λ c, option.get_or_else (dict.get c visited) none) cs,
            b ← z bs,
            pure $ dict.insert h b visited
        end
    end

meta def traverse_down {T} [monad T] {β : Type} (f : V → T (β ⊕ (list β → T β))) (g : G) (v₀ : V) : T β :=
do bs ← traverse_aux (λ v, get_children v g) f ∅ v₀,
    pure $ match (dict.get v₀ bs) with | (some (some x)) := x | _ := undefined end

meta def traverse_up {T} [monad T] {β : Type} (f : V → T (β ⊕ (list β → T β))) (g : G) (v₀ : V) : T β :=
do bs ← traverse_aux (λ v, table.to_list $ get_parents v g) f ∅ v₀,
    pure $ match (dict.get v₀ bs) with | (some (some x)) := x | _ := undefined end

meta def get_greatest_ancestors_aux (g : G) : list V → table V → list V → list V
|[] _ acc := acc
|(h :: front) visited acc :=
    let ps := (get_parents h g) \ visited in
    if ps.is_empty then get_greatest_ancestors_aux front (table.insert h visited) (h::acc)
    else get_greatest_ancestors_aux (front ++ ps.to_list) (table.insert h visited) acc

private meta def is_ancestor_aux (g : G) (v₁ : V) : Π (front : list V) (visited : table V), bool
|[] visited := ff
|(h :: t) visited :=
    if ¬(v₁ < h) ∧ ¬(h < v₁) then tt else
    if h ∈ visited then is_ancestor_aux t visited else
    is_ancestor_aux (table.fold (λ t p, p :: t) t $ get_parents h g) (table.insert h visited)

meta def is_ancestor (v₁ v₂ : V) (g : G) := is_ancestor_aux g v₁ [v₂] ∅

meta def has_loop (v : V) (g : G) := is_ancestor_aux g v (table.to_list (get_parents v g)) ∅

meta def treeify_aux (g : G) : Π (root : V) (visited : table V), (table V) × (tree V)
|root visited :=
    if root ∈ visited then (visited, tree.crossref root) else
    let visited := table.insert root visited in
    let s  := @list.foldr V ((table V) × (list (tree V))) (λ child s, let r := (treeify_aux child s.1) in (r.1, r.2 :: s.2)) (visited,[]) $ get_children root g in
    (s.1, tree.mk root s.2)

/-- Convert to a tree for pretty printing. -/
meta def treeify (root : V) (g : G) := prod.snd $ treeify_aux g root ∅
-- meta instance has_pp [has_to_tactic_format V] : has_to_tactic_format G := ⟨λ g, do
--     -- [todo] handle case where graph is not connected.
--     root ← g.parents.first,
-- ⟩

meta def choose {β} (p : V → option β) : V → G → list β
| v₀ g := option.get_or_else (fold (λ v eo bs, ( :: bs) <$> p v) g v₀ []) []

section widget
  open widget

  meta def tree.view {α γ} (vv : component α γ) : tree α →  (list (html γ))
  | (tree.crossref x) := ["↪", html.of_component x vv]
  | (tree.mk x cs) := [html.of_component x vv,  h "ul" [] $ cs.reverse.map (λ c, h "li" [] $ tree.view c)]

  /-- Show the graph as html. Nothing fancy here, just renders it as a tree. Assuming that `vv` is a small span and that `ev` can be a bit bulkier. -/
  meta def view {γ} (g : G) (root : V) (vv : component V γ) : list (html γ) :=
    let t := treeify root g in
    tree.view vv t

end widget

end GGG

namespace test
    abbreviation V := nat
    meta abbreviation E := table V
    meta instance E_edge_col : edge_col V E := {children := λ e, e.to_list, empty := ∅, push_child := table.insert}
    meta def g : digraph V E := set 1 {} $ set 3 {3} $ set 2 {0,1} $  set 0 {1,2,3} ∅
    meta def assert : bool → tactic unit | tt := pure () | ff := failure
    run_cmd assert (has_loop 3 g)
    run_cmd tactic.pp (treeify 0 g) >>= (λ x, assert $ to_string x = "0[1[], 2[⟨0⟩, ⟨1⟩], 3[⟨3⟩]]")
    run_cmd tactic.pp (treeify 1 g) >>= (λ x, assert $ to_string x = "1[]")
    run_cmd tactic.pp (treeify 2 g) >>= (λ x, assert $ to_string x = "2[0[1[], ⟨2⟩, 3[⟨3⟩]], ⟨1⟩]")
    run_cmd tactic.pp (treeify 3 g) >>= (λ x, assert $ to_string x = "3[⟨3⟩]")

    open widget
    meta def show_g : widget.html empty := widget.h "div" [] $ view g 0 (widget.component.stateless (λ n, [html.of_string $ to_string n]))
    -- #html show_g

    -- run_cmd tactic.trace $ treeify 3 g
end test

end digraph

