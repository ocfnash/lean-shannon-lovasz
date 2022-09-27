import linear_algebra.tensor_power
import analysis.inner_product_space.pi_L2
import to_mathlib.analysis.inner_product_space.tensor_product
import to_mathlib.combinatorics.simple_graph.strong_product
import to_mathlib.combinatorics.simple_graph.independent

noncomputable theory

open set function
open_locale real_inner_product_space tensor_product big_operators

namespace simple_graph

variables {V : Type*} (G : simple_graph V) (E : Type*) [inner_product_space ℝ E]

/-- An orthogonal representation of a graph. -/
structure orthogonal_representation :=
(to_fun : V → E)
(norm_eq_one' : ∀ v, ∥to_fun v∥ = 1)
(inner_eq_zero_of_ne_of_not_adj' : ∀ v w, v ≠ w → ¬ G.adj v w → ⟪to_fun v, to_fun w⟫ = 0)

namespace orthogonal_representation

/-- see Note [function coercion] -/
instance : has_coe_to_fun (orthogonal_representation G E) (λ _, V → E) := ⟨λ ρ, ρ.to_fun⟩

/-- Any finite graph has an orthogonal representation whose dimension is equal to its number of
vertices. The special situation is thus when there is an orthogonal representation into a space
of strictly smaller dimension.

We won't actually need this instance in this project but it might be useful practice to fill in the
proofs below. -/
instance [fintype V] [decidable_eq V] :
  inhabited (G.orthogonal_representation (euclidean_space ℝ V)) :=
⟨{ to_fun := λ v, euclidean_space.single v 1,
   norm_eq_one' := sorry,
   inner_eq_zero_of_ne_of_not_adj' := sorry, }⟩

variables {G E} (ρ : orthogonal_representation G E)

@[simp] lemma norm_eq_one {v : V} : ∥ρ v∥ = 1 :=
ρ.norm_eq_one' v

lemma inner_eq_zero_of_ne_of_not_adj {v w : V} (h₁ : v ≠ w) (h₂ : ¬ G.adj v w) :
  ⟪ρ v, ρ w⟫ = 0 :=
ρ.inner_eq_zero_of_ne_of_not_adj' v w h₁ h₂

/-- The Lovász number of an orthogonal representation of a graph at a vector `e`. -/
def lovasz_number_at (e : E) : ℝ :=
⨆ v, ∥e∥^2 / ⟪ρ v, e⟫^2

@[simp] lemma lovasz_number_at_nneg (e : E) :
  0 ≤ ρ.lovasz_number_at e :=
  begin
    unfold lovasz_number_at,
    apply real.Sup_nonneg,
    intro,
    unfold range,
    intro h₀,
    cases h₀ with v h,
    rw ← div_pow at h,
    rw ← h,
    apply sq_nonneg,
  end

lemma lovasz_number_at_eq_csupr (e : E) :
  ρ.lovasz_number_at e = ⨆ v, ∥e∥^2 / ⟪ρ v, e⟫^2 :=
rfl

lemma independence_number_le_lovasz_number_at (e : E) :
  (G.independence_number : ℝ) ≤ ρ.lovasz_number_at e :=
sorry

variables {W F : Type*} {H : simple_graph W}
variables [inner_product_space ℝ F] (ρ' : orthogonal_representation H F)

/-- If `ρ` is an orthogonal representation of a graph `G` in `E` and `ρ'` is an orthogonal
representation of a graph `H` in `F`, then `(x, y) ↦ (ρ x) ⊗ₜ (ρ' y)` defines an orthogonal
representation of the graph `G.strong_prod H` on `E ⊗ F`.

Actually we probably won't need this definition for this project but it might be good practice
to fill in the proofs below. -/
def prod : orthogonal_representation (G.strong_prod H) (E ⊗[ℝ] F) :=
{ to_fun := λ x, (ρ x.1) ⊗ₜ (ρ' x.2),
  norm_eq_one' := sorry,
  inner_eq_zero_of_ne_of_not_adj' := sorry, }

@[simp] lemma prod_lovasz_number_at [finite V] [finite W] (e : E) (f : F) :
  (ρ.prod ρ').lovasz_number_at (e ⊗ₜ f) = (ρ.lovasz_number_at e) * (ρ'.lovasz_number_at f) :=
sorry

/-- If `ρ` is an orthogonal representation of a graph `G` in `E`, then
`(x₁, x₂, …, xₖ) ↦ (ρ x₁) ⊗ (ρ x₂) ⊗ ⋯ ⊗ (ρ xₖ)` defines an orthogonal representation of the strong
product `G ⊠ G ⊠ ⋯ ⊠ G` in `E ⊗ E ⊗ ⋯ ⊗ E`. -/
def pow (k : ℕ) : orthogonal_representation (⊠^k G) (⨂[ℝ]^k E) :=
{ to_fun := λ x, tensor_power.tpow ℝ (ρ ∘ x),
  norm_eq_one' := sorry,
  inner_eq_zero_of_ne_of_not_adj' := sorry, }

@[simp] lemma pow_lovasz_number_at {k : ℕ} [finite V] (e : fin k → E) :
  (ρ.pow k).lovasz_number_at (tensor_power.tpow ℝ e) = ∏ i, ρ.lovasz_number_at (e i) :=
sorry

lemma pow_lovasz_number_at' {k : ℕ} [finite V] (e : E) :
  (ρ.pow k).lovasz_number_at (tensor_power.tpow ℝ (λ i, e)) = (ρ.lovasz_number_at e)^k :=
sorry

end orthogonal_representation

end simple_graph
