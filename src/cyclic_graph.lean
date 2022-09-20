import combinatorics.simple_graph.basic

noncomputable theory

open set function

def cyclic_graph (n : ℕ) : simple_graph (fin n) :=
{ adj := λ x y, (x - y : ℕ) = 1 ∨ (y - x : ℕ) = 1,
  symm := λ x y h, (or_comm _ _).mp h,
  loopless := λ x, by simp, }
