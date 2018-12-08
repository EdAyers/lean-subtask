/- 
General implementation of a directed graph using adjacency lists.

Authors: E.W.Ayers
 -/
import .table

section digraph_data
/- The type of vertices. -/
variables (V : Type) [has_lt V] [decidable_rel ((<) : V → V → Prop)]  
/- The type of edges. -/
variable (E : Type)
/-- `edge_col V E` identifies a set of child vertices for each edge. -/
meta class edge_col :=
(children : E → list V)
-- [TODO] consult with knowledgable people to see if this can be made more efficient. There is probably some task-dependent structure that I am not taking advantage of.
/-- A directed graph represented as a dictionary of adjacency lists.  -/
meta structure digraph [edge_col V E] :=
(edges : dict V E)
(parents : dict V (table V)) -- revese lookup calculated automatically.
end digraph_data
namespace digraph
section
parameters {V : Type} [has_lt V] [decidable_rel ((<) : V → V → Prop)] {E : Type} [edge_col V E]
local notation `G` := digraph V E
meta def children (e : E) := edge_col.children V e
meta def empty : G := {edges := ∅, parents := ∅}
meta def get_parents (v : V) (g : G) : table V := ∅ <| g.parents.get v
meta def get_children (v : V) (g :G) : list V := [] <| (children <$> g.edges.get v)
meta def set (v : V) (e : E) (g : G) : G :=
    let prev_children := table.from_list $ get_children v g in
    let new_children := table.from_list $ children e in
    let add_these := new_children - prev_children in
    let remove_these := prev_children - new_children in
    let parents := g.parents in
    let parents := table.fold (dict.modify_when_present (table.erase v)) parents remove_these in
    let parents := table.fold (dict.modify (λ t, table.insert v $ option.lhoare ∅ $ t)) parents add_these in
    { edges := dict.insert v e g.edges
    , parents := parents
    }
meta def unset (v : V) (g : G) : G :=
    { edges := dict.erase v g.edges
    , parents := list.foldl (λ parents child, dict.modify_when_present (table.erase v) child parents) g.parents (g.get_children v)
    }
private meta def is_ancestor_aux (g : G) (v₁ : V) : Π (front : list V) (visited : table V), bool
|[] visited := ff
|(h :: t) visited :=
    if ¬(v₁ < h) ∧ ¬(h < v₁) then tt else
    if h ∈ visited then is_ancestor_aux t visited else
    is_ancestor_aux (table.fold (::) t $ get_parents h g) $ table.insert h visited
/-- Returns tt if there exists a directed path `v₁ -> -> v₂`. -/
meta def is_ancestor (v₁ v₂ : V) (g : G) := is_ancestor_aux g v₁ [v₂] ∅
/-- Returns tt if there exists a (non-reflexive) directed path `v -> -> v`. -/
meta def has_loop (v : V) (g : G) := is_ancestor_aux g v (table.to_list (get_parents v g)) ∅

end
end digraph