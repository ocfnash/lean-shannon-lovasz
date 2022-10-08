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

@[simp] lemma norm_e₁ : ∥e₁∥ = 1 :=
  by simp [e₁, euclidean_space.norm_eq, finset.filter_eq']

/-- The Lovász umbrella. -/
def lovasz_umbrella : orthogonal_representation 𝔾₅ 𝔼³ :=
{ to_fun := λ i j, sorry, -- See: https://en.wikipedia.org/wiki/Lov%C3%A1sz_number#Relation_to_Shannon_capacity
  norm_eq_one' := sorry,
  inner_eq_zero_of_ne_of_not_adj' := sorry, }

/-- Proving this will probably require explicit results about the sine or cosine of
`π / 5`, `2 * π / 5`, etc. -/
@[simp] lemma inner_lovasz_umbrella_e₁ (i : fin 5) :
  ⟪lovasz_umbrella i, e₁⟫^2 = 1 / sqrt 5 :=
sorry

@[simp] lemma lovasz_number_at_lovasz_umbrella_eq :
  lovasz_umbrella.lovasz_number_at e₁ = sqrt 5 :=
begin
  dunfold simple_graph.orthogonal_representation.lovasz_number_at,
  simp_rw [inner_lovasz_umbrella_e₁, ←inv_eq_one_div, div_inv_eq_mul],
  rw [show ∥e₁∥ = 1, from _],
  simp_rw [pow_two, one_mul],
  rw [supr, real.Sup_def, dif_pos],
  generalize_proofs h,
  refine le_antisymm _ _,
  { refine h.some_spec.2 _, rintros _ ⟨y, rfl⟩, exact le_refl _, },
  { exact h.some_spec.1 ⟨0, rfl⟩, },
  { refine ⟨⟨_, ⟨0, rfl⟩⟩, ⟨sqrt 5, _⟩⟩,
    rintros _ ⟨y, rfl⟩, refl, },
  { erw [norm_eq_sqrt_real_inner, sqrt_eq_iff_mul_self_eq, one_mul,
      euclidean_space.inner_single_left, map_one, one_mul],
    dunfold e₁, rw [euclidean_space.single_apply, if_pos rfl],
    exact real_inner_self_nonneg, norm_num },
end

lemma strong_pow_two_independence_number :
  5 ≤ (⊠^2 (cyclic 5)).independence_number := sorry

/-- The easier direction.

Easy on paper, not necessarily in Lean. -/
lemma le_shannon_capacity_cyclic_graph_five :
  sqrt 5 ≤ shannon_capacity 𝔾₅ :=
begin
  dunfold shannon_capacity, rw [supr],
  rw le_cSup_iff,
  { intros b hb,
    have := (lovasz_umbrella).independence_number_le_lovasz_number_at e₁,
    specialize @hb _ ⟨1, rfl⟩, dsimp only at hb,
    rw [show 1 + 1 = 2, from rfl, show (↑(1 : ℕ) : ℝ) = 1, by norm_cast,
      show (1 : ℝ) + 1 = 2, by norm_cast, ←sqrt_eq_rpow, sqrt_le_iff] at hb,
    have h2 : (5 : ℝ) ≤ (⊠^2 (cyclic 5)).independence_number :=
      by exact_mod_cast strong_pow_two_independence_number,
    rw sqrt_le_iff, refine ⟨hb.1, h2.trans hb.2⟩ },
  { refine ⟨sqrt 5, _⟩, rintros _ ⟨k, rfl⟩, dsimp only,
    have H := (lovasz_umbrella.pow (k+1)).independence_number_le_lovasz_number_at
      (tensor_power.tpow ℝ (λ _, e₁)),
    rw [orthogonal_representation.pow_lovasz_number_at', lovasz_number_at_lovasz_umbrella_eq] at H,
    refine (real.rpow_le_rpow _ H _).trans _,
    { norm_cast, exact nat.zero_le _, },
    { rw div_nonneg_iff, left, split, norm_num, norm_cast, exact nat.zero_le _, },
    { rw [show sqrt 5 ^ (k + 1) = sqrt 5 ^ (k + 1 : ℝ), by norm_cast, ←real.rpow_mul,
      mul_one_div_cancel, rpow_one], norm_cast,
      linarith, exact sqrt_nonneg _, }, },
  { exact ⟨_, ⟨1, rfl⟩⟩, },
end

/-- The harder direction. -/
lemma shannon_capacity_cyclic_graph_five_le :
  shannon_capacity 𝔾₅ ≤ sqrt 5 :=
begin
  apply (shannon_capacity_le_lovasz_number_at 𝔾₅ lovasz_umbrella e₁).trans,
  apply lovasz_number_at_lovasz_umbrella_eq.le,
end

/-- *Main project goal* -/
@[simp] lemma shannon_capacity_cyclic_graph_five_eq :
  shannon_capacity 𝔾₅ = sqrt 5 :=
le_antisymm shannon_capacity_cyclic_graph_five_le le_shannon_capacity_cyclic_graph_five

/- The `#print` statement below currently produces:
```
classical.choice
quot.sound
propext
[sorry]
```
Our goal is to get it to stop printing the line saying `[sorry]`.
-/
#print axioms shannon_capacity_cyclic_graph_five_eq
