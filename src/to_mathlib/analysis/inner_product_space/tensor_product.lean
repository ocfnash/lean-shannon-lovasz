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
    simp only [finset.sum_map, embedding.coe_fn_mk],
    apply tensor_sum,
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

/- We may not actually need this for this project since what we really want is the `instance`
lower down for the _tensor power_.

This is still a gap in Mathlib that is worth filling. -/

-- new stuff starts here (line 30 in my analysis/inner_product_space/tensor_product file)


-- section some_linear_algebra_from_kevin

-- local attribute [ext] tensor_product.ext

-- /-- Two linear maps (M ⊗ N) ⊗ (P ⊗ Q) → S which agree on all elements of the
-- form (m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q) are equal. -/
-- theorem ext_fourfold' {R M N P Q S: Type*} [comm_semiring R]
--   [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q]
--   [add_comm_monoid S] [module R M] [module R N] [module R P] [module R Q] [module R S]
--   {φ ψ : (M ⊗[R] N) ⊗[R] (P ⊗[R] Q) →ₗ[R] S}
--   (H : ∀ w x y z, φ ((w ⊗ₜ x) ⊗ₜ (y ⊗ₜ z)) = ψ ((w ⊗ₜ x) ⊗ₜ (y ⊗ₜ z))) : φ = ψ :=
-- begin
--   ext m n p q,
--   exact H m n p q,
-- end

-- end some_linear_algebra_from_kevin

/-- We may not actually need this for this project since what we really want is the `instance`
lower down for the _tensor power_.

This is still a gap in Mathlib that is worth filling. -/
--variables (hE : finite_dimensional ℝ E) (hF : finite_dimensional ℝ F)
--include hE hF
-- instance : inner_product_space ℝ (E ⊗[ℝ] F) := of_core
-- { inner := λ x y, tensor_product_aux E F (x ⊗ₜ y),
--   conj_sym :=
--   begin
--     sorry {
--     intros x y,
--     rw [is_R_or_C.conj_to_real],
--     suffices : tensor_product_aux E F =
--       (tensor_product_aux E F).comp (tensor_product.comm _ _ _).to_linear_map,
--     { conv_lhs {rw this},
--       simp, },
--     apply ext_fourfold',
--     intros e₁ f₁ e₂ f₂,
--     suffices : inner e₁ e₂ * inner f₁ f₂ = inner e₂ e₁ * inner f₂ f₁,
--     { simpa },
--     rw [← inner_conj_sym e₁, is_R_or_C.conj_to_real, ← inner_conj_sym f₁, is_R_or_C.conj_to_real],}
--   end,
--   nonneg_re := begin
--     intros z,
--     rw [is_R_or_C.re_to_real],
--     rw [← (basis.of_vector_space ℝ (E ⊗ F)).total_repr z, basis.coe_of_vector_space],
--     rw finsupp.total_apply,
--     sorry
--   end,
--   definite := λ x, begin
--     sorry
--   end,
--   add_left := λ x y z, by rw [tensor_product.add_tmul, map_add],
--   smul_left := λ x y r, by rw [is_R_or_C.conj_to_real,
--     ← tensor_product.smul_tmul', map_smul, smul_eq_mul],}
-- -- omit hE hF


-- -- #check (tensor_product_aux E F).comp (tensor_product.mk ℝ (E ⊗ F) (E ⊗ F))
-- -- #check (tensor_product_aux E F)
-- -- .comp (tensor_product.mk ℝ (E ⊗ F) (E ⊗ F))


-- @[simp] lemma inner_tprod (e₁ e₂ : E) (f₁ f₂ : F) :
--   ⟪e₁ ⊗ₜ[ℝ] f₁, e₂ ⊗ₜ[ℝ] f₂⟫ = ⟪e₁, e₂⟫ * ⟪f₁, f₂⟫ :=
-- tensor_product_aux_apply E F e₁ e₂ f₁ f₂

-- instance (k : ℕ) : inner_product_space ℝ (⨂[ℝ]^k E) := sorry

-- @[simp] lemma inner_tpow {k : ℕ} (e₁ e₂ : fin k → E) :
--   ⟪tensor_power.tpow ℝ e₁, tensor_power.tpow ℝ e₂⟫ = ∏ i, ⟪e₁ i, e₂ i⟫ :=
-- sorry

-- example (E : Type*) (F : Type*)
--   [inner_product_space ℝ E] [finite_dimensional ℝ E]
--   [inner_product_space ℝ F] [finite_dimensional ℝ F] :
--   ∀ (x : E ⊗[ℝ] F),
--     0 ≤ is_R_or_C.re ((tensor_product_aux E F) (x ⊗ₜ[ℝ] x)) :=
-- begin
--   intros x,
--   admit,
-- end
example : true := trivial

end inner_product_space


-- section more_stuff

-- open_locale classical

-- variables {k E : Type*} [field k] [add_comm_group E] [module k E]
-- lemma to_fd (e : E) : ∃ (E' : subspace k E) [finite_dimensional k E'], e ∈ E' := -- this is the μ or η in the paper proof
-- begin
--   refine ⟨submodule.span k ( finset.image (basis.of_vector_space k E) ((basis.of_vector_space k E).repr e).support), _, _⟩,
--   { apply finite_dimensional.span_finset,},
--   { have H := (basis.of_vector_space k E).total_repr e,
--     conv_lhs { rw ← H},
--     rw finsupp.total_apply,
--     convert submodule.sum_mem _ _,
--     intros c hc,
--     convert submodule.smul_mem _ _ _,
--     apply submodule.subset_span,
--     rw [finset.coe_image, set.mem_image],
--     exact ⟨_, hc, rfl⟩},
-- end


-- end more_stuff
