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

/- We may not actually need this for this project since what we really want is the `instance`
lower down for the _tensor power_.

This is still a gap in Mathlib that is worth filling. -/

-- new stuff starts here (line 30 in my analysis/inner_product_space/tensor_product file)


section some_linear_algebra_from_kevin

local attribute [ext] tensor_product.ext

/-- Two linear maps (M ⊗ N) ⊗ (P ⊗ Q) → S which agree on all elements of the
form (m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q) are equal. -/
theorem ext_fourfold' {R M N P Q S: Type*} [comm_semiring R]
  [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q]
  [add_comm_monoid S] [module R M] [module R N] [module R P] [module R Q] [module R S]
  {φ ψ : (M ⊗[R] N) ⊗[R] (P ⊗[R] Q) →ₗ[R] S}
  (H : ∀ w x y z, φ ((w ⊗ₜ x) ⊗ₜ (y ⊗ₜ z)) = ψ ((w ⊗ₜ x) ⊗ₜ (y ⊗ₜ z))) : φ = ψ :=
begin
  ext m n p q,
  exact H m n p q,
end

end some_linear_algebra_from_kevin

/-- We may not actually need this for this project since what we really want is the `instance`
lower down for the _tensor power_.

This is still a gap in Mathlib that is worth filling. -/
instance : inner_product_space ℝ (E ⊗[ℝ] F) := of_core
{ inner := λ x y, tensor_product_aux E F (x ⊗ₜ y),
  conj_sym :=
  begin
    sorry {
    intros x y,
    rw [is_R_or_C.conj_to_real],
    suffices : tensor_product_aux E F =
      (tensor_product_aux E F).comp (tensor_product.comm _ _ _).to_linear_map,
    { conv_lhs {rw this},
      simp, },
    apply ext_fourfold',
    intros e₁ f₁ e₂ f₂,
    suffices : inner e₁ e₂ * inner f₁ f₂ = inner e₂ e₁ * inner f₂ f₁,
    { simpa },
    rw [← inner_conj_sym e₁, is_R_or_C.conj_to_real, ← inner_conj_sym f₁, is_R_or_C.conj_to_real],}
  end,
  nonneg_re := begin
    intro x,
    rw [is_R_or_C.re_to_real],
    -- have H1 := (tensor_product_aux E F).comp (tensor_product.mk ℝ (E ⊗ F) (E ⊗ F) x),
    induction x using tensor_product.induction_on with e f x₁ x₂ hx₁ hx₂,
    { rw [tensor_product.tmul_zero, map_zero]},
    { rw tensor_product_aux_apply,
      exact mul_nonneg real_inner_self_nonneg real_inner_self_nonneg,},
    { simp only [tensor_product.add_tmul, tensor_product.tmul_add, map_add],
      apply add_nonneg,
      { apply add_nonneg hx₁,

        sorry,
      },
      { apply add_nonneg _ hx₂,
        sorry,}
    },
  end,
  definite := sorry,
  add_left := sorry,
  smul_left := sorry, }


-- #check (tensor_product_aux E F).comp (tensor_product.mk ℝ (E ⊗ F) (E ⊗ F))
-- #check (tensor_product_aux E F)
-- .comp (tensor_product.mk ℝ (E ⊗ F) (E ⊗ F))

#exit

@[simp] lemma inner_tprod (e₁ e₂ : E) (f₁ f₂ : F) :
  ⟪e₁ ⊗ₜ[ℝ] f₁, e₂ ⊗ₜ[ℝ] f₂⟫ = ⟪e₁, e₂⟫ * ⟪f₁, f₂⟫ :=
tensor_product_aux_apply E F e₁ e₂ f₁ f₂

instance (k : ℕ) : inner_product_space ℝ (⨂[ℝ]^k E) := sorry

@[simp] lemma inner_tpow {k : ℕ} (e₁ e₂ : fin k → E) :
  ⟪tensor_power.tpow ℝ e₁, tensor_power.tpow ℝ e₂⟫ = ∏ i, ⟪e₁ i, e₂ i⟫ :=
sorry

end inner_product_space
