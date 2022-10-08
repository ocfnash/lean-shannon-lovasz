import combinatorics.simple_graph.basic

noncomputable theory

open set function

namespace simple_graph

/-- The cyclic graph with `n` vertices.

This is just one possible model: we might want to consider others. -/
@[simps] def cyclic (n : ℕ) : simple_graph (fin n) :=
{ adj := λ x y, (↑(x - y) : ℕ) = 1 ∨ (↑(y - x) : ℕ) = 1,
  symm := λ x y, (or_comm _ _).mp,
  loopless := λ x , by {
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

lemma not_cyclic_5_adj_0_2 : ¬(cyclic 5).adj 0 2 :=
begin
  simp only [cyclic_adj, zero_sub, sub_zero, fin.coe_two, nat.succ_succ_ne_one, or_false],
  rw [fin.coe_neg], simp only [fin.coe_two, nat.succ_sub_succ_eq_sub, tsub_zero],
  intros r, have : 3 % 5 = 3 := rfl, rw this at r, norm_num at r,
end

@[simp] lemma coe_four  {n : ℕ} : ((4 : fin (n+5)) : ℕ) = 4 := rfl
@[simp] lemma coe_three {n : ℕ} : ((3 : fin (n+4)) : ℕ) = 3 := rfl

lemma not_cyclic_5_adj_0_3 : ¬(cyclic 5).adj 0 3 :=
begin
  simp only [cyclic_adj, zero_sub, sub_zero, coe_three, nat.bit1_eq_one, nat.one_ne_zero, or_false],
  rw [fin.coe_neg],
  simp only [coe_three, nat.succ_sub_succ_eq_sub, tsub_zero],
  intros r, have : 2 % 5 = 2 := rfl, rw this at r, norm_num at r,
end

end simple_graph
