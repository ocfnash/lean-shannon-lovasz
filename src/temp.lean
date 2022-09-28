import analysis.special_functions.trigonometric.basic
import analysis.normed_space.pi_Lp
import to_mathlib.combinatorics.simple_graph.cyclic
import to_mathlib.combinatorics.simple_graph.shannon_capacity

@[simp] lemma pi_Lp.norm_single {ι : Type _} {p : ennreal} {β : ι → Type _}
  [fintype ι] [decidable_eq ι] [Π (i : ι), seminormed_add_comm_group (β i)]
  (i : ι) (v : β i) (hp : 0 < p.to_real) :
  ∥(id (pi.single i v) : pi_Lp p β)∥ = ∥v∥ :=
begin
  rw [pi_Lp.norm_eq_sum hp,
      ←finset.filter_union_filter_neg_eq (λ j, j = i) finset.univ,
      finset.sum_union (finset.disjoint_filter_filter_neg _ _),
      finset.filter_eq', if_pos (finset.mem_univ _), finset.sum_singleton],
  rw finset.sum_eq_zero,
  { norm_num,
    rw [←real.rpow_mul, mul_one_div_cancel (ne_of_lt hp).symm],
    norm_num,
    exact norm_nonneg _, },
  { intros x hx,
    simp only [id],
    rw [pi.single_eq_of_ne (finset.mem_filter.mp hx).2,
        norm_zero,
        real.zero_rpow (ne_of_lt hp).symm], },
end

@[simp] lemma euclidean_space.norm_single'
  (𝕜 : Type _) (ι : Type _) [fintype ι] [decidable_eq ι] (i : ι) (k : 𝕜) [is_R_or_C 𝕜] :
  ∥euclidean_space.single i k∥ = ∥k∥
:= begin
  have h := pi_Lp.norm_single i k (by norm_num : 0 < ennreal.to_real 2),
  exact h,
end
