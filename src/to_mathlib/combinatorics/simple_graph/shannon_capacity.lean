import analysis.special_functions.pow
import to_mathlib.combinatorics.simple_graph.independent
import to_mathlib.combinatorics.simple_graph.orthogonal_representation

noncomputable theory

open set function real

variables {V : Type*} (G : simple_graph V)

namespace simple_graph

/-- The Shannon capacity of a graph. -/
def shannon_capacity : ℝ :=
⨆ k, (⊠^(k+1) G).independence_number ^ ((1 : ℝ) / (k + 1))

lemma shannon_capacity_eq_csupr :
  G.shannon_capacity = ⨆ k, (⊠^(k+1) G).independence_number ^ ((1 : ℝ) / (k + 1)) :=
rfl

variables [finite V] {E : Type*} [inner_product_space ℝ E]
variables (ρ : G.orthogonal_representation E) (e : E)

lemma shannon_capacity_le_lovasz_number_at :
  G.shannon_capacity ≤ ρ.lovasz_number_at e :=
begin
  -- Use the definition of Shannon capacity:
  rw G.shannon_capacity_eq_csupr,
  -- If we want to prove a supremum is bounded above, it is enough to bound each term:
  refine csupr_le (λ k, _),
  -- Raise both sides of the inequality to the power `k+1` and tidy up:
  have hk : 0 < (k + 1 : ℝ) := k.cast_add_one_pos,
  rw [← rpow_le_rpow_iff
    (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) (ρ.lovasz_number_at_nneg e) hk,
    ← rpow_mul (nat.cast_nonneg _), div_mul_cancel (1 : ℝ) hk.ne.symm, rpow_one],
  -- Eliminate casts
  norm_cast,
  -- Apply first key fact; the Lovász number is multiplicative `ϑ(⊠ᵏG, ⊠ᵏρ, e^k) = ϑ(G, ρ, e)^k`:
  rw ← ρ.pow_lovasz_number_at' e,
  -- Apply second key fact; the independence number of a graph is bounded by the Lovász number:
  apply orthogonal_representation.independence_number_le_lovasz_number_at,
end

end simple_graph
