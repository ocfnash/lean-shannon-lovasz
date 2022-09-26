import analysis.special_functions.trigonometric.basic
import analysis.normed_space.lp_space
import to_mathlib.combinatorics.simple_graph.cyclic
import to_mathlib.combinatorics.simple_graph.shannon_capacity

noncomputable theory

open set function real simple_graph
open_locale real_inner_product_space

local notation `𝔼³` := euclidean_space ℝ $ fin 3
local notation `𝔾₅` := simple_graph.cyclic 5

/-- Standard basis element. -/
def e₁ : 𝔼³ := euclidean_space.single 0 1

/-- Standard basis element. -/
def e₂ : 𝔼³ := euclidean_space.single 1 1

/-- Standard basis element. -/
def e₃ : 𝔼³ := euclidean_space.single 2 1

@[simp] lemma euclidean_space.norm_single
  (𝕜 : Type _) (ι : Type _) [fintype ι] [decidable_eq ι] (i : ι) (k : 𝕜) [is_R_or_C 𝕜] :
  ∥euclidean_space.single i k∥ = k^2 :=
begin
  rw euclidean_space.norm_eq,
  rw ←finset.filter_union_filter_neg_eq (λ j, j = i) finset.univ,
  rw finset.sum_union,
  { simp,
    rw finset.filter_eq',
    simp,
    rw finset.sum_eq_zero,
    swap,
    { intros,
      simp at H,
      rw if_neg H,
      norm_num, },
    { norm_num, } },
  { sorry, }
end
