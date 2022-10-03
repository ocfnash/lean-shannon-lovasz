import analysis.inner_product_space.basic
import algebra.algebra.bilinear
import to_mathlib.linear_algebra.tensor_power
import linear_algebra.finite_dimensional

noncomputable theory

open set function
open_locale real_inner_product_space tensor_product big_operators

namespace inner_product_space

lemma tensor_sum {α β H I : Type*} {α : Type*}
  [add_comm_monoid H] [add_comm_monoid I] [module ℝ H] [module ℝ I]
  (s : finset α) (e : H) (f : α → I) :
  e ⊗ₜ[ℝ] ∑ a in s, f a = ∑ a in s, e ⊗ₜ f a :=
begin
  classical,
  refine finset.induction_on s _ _,
  { rw [finset.sum_empty, tensor_product.tmul_zero, finset.sum_empty], },
  { intros a s' ha ih,
    rw [finset.sum_insert, tensor_product.tmul_add, ih, finset.sum_insert];
    assumption },
end

lemma sum_tensor_sum {α β H I : Type*}
  [add_comm_monoid H] [add_comm_monoid I] [module ℝ H] [module ℝ I]
  (s : finset α) (t : finset β)
  (f : α → H) (g : β → I) :
  (∑ a in s, f a) ⊗ₜ[ℝ] (∑ b in t, g b) =
  (∑ x in finset.product s t, (f x.1) ⊗ₜ[ℝ] (g x.2)) :=
begin
  classical,
  induction s using finset.induction_on with a s' ha ih,
  { rw [finset.sum_empty, tensor_product.zero_tmul, finset.empty_product,
      finset.sum_empty], },
  { rw [finset.sum_insert, tensor_product.add_tmul, ih],
    have : ∑ (x : α × β) in insert a s' ×ˢ t, f x.fst ⊗ₜ[ℝ] g x.snd =
      ∑ (x : α × β) in (s' ×ˢ t) ∪ ({a} ×ˢ t), f x.fst ⊗ₜ g x.snd,
    { apply finset.sum_bij',
      work_on_goal 4
      { refine λ x hx, x, },
      work_on_goal 5
      { refine λ x hx, x, },
      { rintros ⟨a, b⟩ h, refl, },
      { rintros ⟨a, b⟩ h, refl, },
      { rintros ⟨a, b⟩ h, refl, },
      { rintros ⟨a, b⟩ h,
        simp only [finset.singleton_product, finset.mem_union, finset.mem_product, finset.mem_map,
          embedding.coe_fn_mk, prod.mk.inj_iff, exists_prop, exists_eq_right_right,
          finset.mem_insert] at h ⊢,
        tauto, },
      { rintros ⟨a, b⟩ h,
        simp only [finset.mem_product, finset.mem_insert, finset.singleton_product,
          finset.mem_union, finset.mem_map, embedding.coe_fn_mk, prod.mk.inj_iff, exists_prop,
          exists_eq_right_right] at h ⊢,
        tauto, }, },
    rw [this, finset.sum_union, finset.singleton_product, add_comm],
    congr' 1,
    rw [finset.sum_map, tensor_sum], refl, exact H, exact I,
    { rw finset.disjoint_iff_inter_eq_empty,
      rw finset.eq_empty_iff_forall_not_mem,
      rintros ⟨a', b'⟩ r,
      simp only [finset.singleton_product, finset.mem_inter, finset.mem_product, finset.mem_map,
        embedding.coe_fn_mk, prod.mk.inj_iff, exists_prop, exists_eq_right_right] at r,
      rcases r with ⟨⟨ha', _⟩, _, rfl⟩,
      exact ha ha', },
    assumption },
end

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

-- instance (k : ℕ) : inner_product_space ℝ (⨂[ℝ]^k E) := sorry

-- @[simp] lemma inner_tpow {k : ℕ} (e₁ e₂ : fin k → E) :
--   ⟪tensor_power.tpow ℝ e₁, tensor_power.tpow ℝ e₂⟫ = ∏ i, ⟪e₁ i, e₂ i⟫ :=
-- sorry


end inner_product_space
