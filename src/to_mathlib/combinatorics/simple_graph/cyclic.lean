import combinatorics.simple_graph.basic

noncomputable theory

open set function

namespace simple_graph

/-- The cyclic graph with `n` vertices.

This is just one possible model: we might want to consider others. -/
def cyclic (n : ℕ) : simple_graph (fin n) :=
{ adj := λ x y, (↑(x - y) : ℕ) = 1 ∨ (↑(y - x) : ℕ) = 1,
  symm := λ x y, (or_comm _ _).mp,
  loopless := λ x, by sorry, }

end simple_graph
