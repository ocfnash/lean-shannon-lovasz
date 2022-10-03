import to_mathlib.analysis.inner_product_space.tensor_product_of_inner_product_finite_dimensional
import to_mathlib.linear_algebra.tensor_power
import algebra.big_operators.fin

noncomputable theory

open set function
open_locale real_inner_product_space tensor_product big_operators

namespace tensor_power

variables (E : Type*) [inner_product_space ℝ E]

def tensor_power0_inner : inner_product_space.core ℝ (⨂[ℝ]^0 E) :=
{ inner := λ x y, pi_tensor_product.is_empty_equiv (fin 0) x * pi_tensor_product.is_empty_equiv (fin 0) y,
  conj_sym := sorry,
  nonneg_re := sorry,
  definite := sorry,
  add_left := sorry,
  smul_left := sorry }

def tensor_power_succ_inner (k : ℕ) (core_k : inner_product_space.core ℝ (⨂[ℝ]^k E)) :
  inner_product_space.core ℝ (⨂[ℝ]^k.succ E) :=
let l : ⨂[ℝ]^k.succ E ≃ₗ[ℝ] ⨂[ℝ]^k E ⊗[ℝ] E :=
  linear_equiv.trans ((@tensor_power.mul_equiv ℝ E _ _ _ k 1)).symm
    (linear_equiv.of_linear
      (tensor_product.lift
      { to_fun := λ x,
        { to_fun := λ y, x ⊗ₜ pi_tensor_product.subsingleton_equiv (0 : fin 1) y,
          map_add' := sorry,
          map_smul' := sorry },
        map_add' := sorry,
        map_smul' := sorry })
    (tensor_product.lift
      { to_fun := λ x,
        { to_fun := λ y, x ⊗ₜ (pi_tensor_product.subsingleton_equiv (0 : fin 1)).symm y,
          map_add' := sorry,
          map_smul' := sorry },
        map_add' := sorry,
        map_smul' := sorry }) sorry sorry : ⨂[ℝ]^k E ⊗ ⨂[ℝ]^1 E ≃ₗ[ℝ] ⨂[ℝ]^k E ⊗ E),
  i1 : inner_product_space ℝ (⨂[ℝ]^k E ⊗[ℝ] E) :=
    @inner_product_space.tensor_product' (⨂[ℝ]^k E) E (inner_product_space.of_core core_k) _ in
{ inner := λ x y, i1.inner (l x) (l y),
  conj_sym := sorry,
  nonneg_re := sorry,
  definite := sorry,
  add_left := sorry,
  smul_left := sorry }

instance (k : ℕ) : inner_product_space ℝ (⨂[ℝ]^k E) := inner_product_space.of_core
begin
  induction k, apply tensor_power0_inner,
  apply tensor_power_succ_inner, assumption,
end

@[simp] lemma inner_tpow {k : ℕ} (e₁ e₂ : fin k → E) :
  ⟪tensor_power.tpow ℝ e₁, tensor_power.tpow ℝ e₂⟫ = ∏ i, ⟪e₁ i, e₂ i⟫ :=
begin
  revert e₁ e₂, induction k,
  { intros e₁ e₂, rw [fin.prod_univ_zero], sorry },
  { sorry }
end


end tensor_power
