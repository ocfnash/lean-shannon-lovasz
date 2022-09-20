import analysis.inner_product_space.basic
import algebra.algebra.bilinear
import to_mathlib.linear_algebra.tensor_power

noncomputable theory

open set function
open_locale real_inner_product_space tensor_product big_operators

namespace inner_product_space

variables (E F : Type*) [inner_product_space ℝ E] [inner_product_space ℝ F]

/-- We can regard the bilinear form of a real inner product space as a linear map on the tensor
square. -/
def as_tensor : E ⊗[ℝ] E →ₗ[ℝ] ℝ :=
tensor_product.lift bilin_form_of_real_inner.to_lin

/-- An auxiliary definition used to help construct the `inner_product_space` on the binary tensor
product below. -/
def tensor_product_aux : (E ⊗[ℝ] F) ⊗[ℝ] (E ⊗[ℝ] F) →ₗ[ℝ] ℝ :=
linear_map.mul' ℝ ℝ ∘ₗ
(tensor_product.map (as_tensor E) (as_tensor F)) ∘ₗ
↑(tensor_product.tensor_tensor_tensor_comm ℝ E F E F)

@[simp] lemma tensor_product_aux_apply (e₁ e₂ : E) (f₁ f₂ : F) :
  tensor_product_aux E F ((e₁ ⊗ₜ[ℝ] f₁) ⊗ₜ[ℝ] (e₂ ⊗ₜ[ℝ] f₂)) = ⟪e₁, e₂⟫ * ⟪f₁, f₂⟫ :=
by simp [tensor_product_aux, as_tensor]

/-- We may not actually need this for this project since what we really want is the `instance`
lower down for the _tensor power_.

This is still a gap in Mathlib that is worth filling. -/
instance : inner_product_space ℝ (E ⊗[ℝ] F) := of_core
{ inner := λ x y, tensor_product_aux E F (x ⊗ₜ y),
  conj_sym := sorry,
  nonneg_re := sorry,
  definite := sorry,
  add_left := sorry,
  smul_left := sorry, }

@[simp] lemma inner_tprod (e₁ e₂ : E) (f₁ f₂ : F) :
  ⟪e₁ ⊗ₜ[ℝ] f₁, e₂ ⊗ₜ[ℝ] f₂⟫ = ⟪e₁, e₂⟫ * ⟪f₁, f₂⟫ :=
tensor_product_aux_apply E F e₁ e₂ f₁ f₂

instance (k : ℕ) : inner_product_space ℝ (⨂[ℝ]^k E) := sorry

@[simp] lemma inner_tpow {k : ℕ} (e₁ e₂ : fin k → E) :
  ⟪tensor_power.tpow ℝ e₁, tensor_power.tpow ℝ e₂⟫ = ∏ i, ⟪e₁ i, e₂ i⟫ :=
sorry

end inner_product_space
