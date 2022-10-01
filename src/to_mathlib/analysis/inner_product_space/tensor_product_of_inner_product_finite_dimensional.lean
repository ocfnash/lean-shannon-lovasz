import to_mathlib.analysis.inner_product_space.tensor_product
import analysis.inner_product_space.gram_schmidt_ortho

noncomputable theory

open_locale real_inner_product_space tensor_product big_operators

namespace inner_product_space

variables (E F : Type*) [linear_order E] [linear_order F]
variables [inner_product_space ℝ E] [inner_product_space ℝ F]
variables [finite_dimensional ℝ E] [finite_dimensional ℝ F]

lemma reduce_E_tensor_F (z : E ⊗[ℝ] F) :
  ∃ (s : finset $ fin (finite_dimensional.finrank ℝ E))
    (t : finset $ fin (finite_dimensional.finrank ℝ F))
    (cE : fin (finite_dimensional.finrank ℝ E) → ℝ)
    (cF : fin (finite_dimensional.finrank ℝ F) → ℝ),
    z = ∑ i in s ×ˢ t, (cE i.1 * cF i.2) •
      (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E) i.1 ⊗ₜ
       gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F) i.2) :=
begin
  set ι_E := fin (finite_dimensional.finrank ℝ E),
  set ι_F := fin (finite_dimensional.finrank ℝ F),
  set onb_E := gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E),
  set onb_F := gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F),
  induction z using tensor_product.induction_on with e f z₁ z₂ ih₁ ih₂,
  { refine ⟨∅, ∅, 0, 0, _⟩,
    rw [finset.empty_product, finset.sum_empty], },
  { set s_e := (onb_E.to_basis.repr e).support,
    set s_f := (onb_F.to_basis.repr f).support,
    refine ⟨s_e, s_f, λ i, onb_E.to_basis.repr e i, λ j, onb_F.to_basis.repr f j, _⟩,
    convert_to e ⊗ₜ[ℝ] f = ∑ (i : ι_E × ι_F) in s_e ×ˢ s_f,
      (onb_E.to_basis.repr e i.fst • onb_E i.fst) ⊗ₜ (onb_F.to_basis.repr f i.snd • onb_F i.snd),
    { refine finset.sum_congr rfl _, rintros ⟨i, j⟩ h,
      simp only [mul_smul, tensor_product.smul_tmul, tensor_product.tmul_smul],
      simp only [←mul_smul, mul_comm], },
    conv_lhs { rw [←onb_E.to_basis.total_repr e, ←onb_F.to_basis.total_repr f] },
    rw [finsupp.total_apply, finsupp.total_apply, finsupp.sum, finsupp.sum, sum_tensor_sum],
    refine finset.sum_congr rfl _,
    rintros ⟨i, j⟩ h, dsimp only, congr' 2; simp only [orthonormal_basis.coe_to_basis] },
  { rcases ih₁ with ⟨s₁, t₁, cE₁, cF₁, ih₁⟩, rcases ih₂ with ⟨s₂, t₂, cE₂, cF₂, ih₂⟩,
    refine ⟨s₁ ∪ s₂, t₁ ∪ t₂, _, _, _⟩, sorry, sorry, sorry }
end

instance tensor_product_of_finite : inner_product_space ℝ (E ⊗[ℝ] F) :=
of_core
{ inner := λ x y, tensor_product_aux E F (x ⊗ₜ y),
  conj_sym := λ z₁ z₂, tensor_product.induction_on z₁
    (by rw [tensor_product.tmul_zero, map_zero, map_zero, tensor_product.zero_tmul, map_zero])
    (λ x y, tensor_product.induction_on z₂
      (by rw [tensor_product.zero_tmul, map_zero, map_zero, tensor_product.tmul_zero, map_zero])
      (λ e f, by { rw [tensor_product_aux_apply, tensor_product_aux_apply, star_ring_end_apply],
        dsimp, rw [real_inner_comm f y, real_inner_comm e x], })
      (λ x₁ x₂ ih₁ ih₂, by rw [tensor_product.add_tmul, map_add, map_add, ih₁, ih₂,
        tensor_product.tmul_add, map_add]))
    (λ x y ih₁ ih₂, by rw [tensor_product.tmul_add, map_add, map_add, ih₁, ih₂,
      tensor_product.add_tmul, map_add]),
  nonneg_re := begin
    intros z, classical,
    set onb_E := gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E),
    set onb_F := gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F),
    rw [is_R_or_C.re_to_real],
    obtain ⟨s, t, cE, cF, rfl⟩ := reduce_E_tensor_F E F z,
    rw [sum_tensor_sum, map_sum],
    simp_rw [tensor_product.smul_tmul, tensor_product.tmul_smul, map_smul, ←mul_smul,
      tensor_product_aux_apply],
    change (0 : ℝ) ≤ ∑ x in (s ×ˢ t) ×ˢ s ×ˢ t, (cE x.1.1 * cF x.1.2 * (cE x.2.1 * cF x.2.2)) •
        (inner (onb_E x.1.1) (onb_E x.2.1) * inner (onb_F x.1.2) (onb_F x.2.2)),
    have : ∀ x : (fin (finite_dimensional.finrank ℝ E) × fin (finite_dimensional.finrank ℝ F)) ×
        fin (finite_dimensional.finrank ℝ E) × fin (finite_dimensional.finrank ℝ F),
      inner (onb_E x.fst.fst) (onb_E x.snd.fst) * inner (onb_F x.fst.snd) (onb_F x.snd.snd) =
      if x.1.1 = x.2.1 ∧ x.1.2 = x.2.2 then (1 : ℝ) else (0 : ℝ),
      { rintros ⟨⟨a, b⟩, ⟨c, d⟩⟩, dsimp only,
        rw [orthonormal_iff_ite.mp onb_E.orthonormal, orthonormal_iff_ite.mp onb_F.orthonormal,
          ite_mul, one_mul, zero_mul, ite_and], },
    simp_rw [this, smul_ite, smul_eq_mul, mul_one, mul_zero],
    rw [finset.sum_ite, finset.sum_const_zero, add_zero],
    apply finset.sum_nonneg,
    rintros ⟨⟨a, b⟩, ⟨c, d⟩⟩ h,
    simp only [finset.mem_filter, finset.mem_product] at h, dsimp only,
    rw [h.2.1, h.2.2, show ∀ (a b c d : ℝ), a * b * (c * d) = (a * c) * (b * d), by intros; ring1],
    exact mul_nonneg (mul_self_nonneg (cE c)) (mul_self_nonneg (cF d)),
  end,
  definite := λ x, begin
    sorry
  end,
  add_left := λ x y z, by rw [tensor_product.add_tmul, map_add],
  smul_left := λ x y r, by rw [is_R_or_C.conj_to_real,
    ← tensor_product.smul_tmul', map_smul, smul_eq_mul],}

end inner_product_space
