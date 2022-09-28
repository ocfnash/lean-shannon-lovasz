import combinatorics.simple_graph.basic

noncomputable theory

open set function

namespace simple_graph

/-- The cyclic graph with `n` vertices.

This is just one possible model: we might want to consider others. -/
def cyclic (n : ℕ) : simple_graph (fin n) :=
{ adj := λ x y, (↑(x - y) : ℕ) = 1 ∨ (↑(y - x) : ℕ) = 1,
  symm := λ x y, (or_comm _ _).mp,
  loopless := λ x, by {
    simp only [or_self],
   -- unfold has_sub.sub,
    intro contra,
    have h : x ≤ x,
    {refl},
    rw ← fin.coe_sub_iff_le at h,
    rw h at contra,
    simp only [tsub_self, nat.zero_ne_one] at contra,
    exact contra,
    }, }

end simple_graph
