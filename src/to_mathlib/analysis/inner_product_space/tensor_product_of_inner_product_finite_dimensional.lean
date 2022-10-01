import to_mathlib.analysis.inner_product_space.tensor_product
import analysis.inner_product_space.gram_schmidt_ortho

noncomputable theory

open_locale real_inner_product_space tensor_product big_operators

namespace inner_product_space

variables (E F : Type*) [linear_order E] [linear_order F]
variables [inner_product_space ℝ E] [inner_product_space ℝ F]

section finite

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
    refine ⟨s₁ ∪ s₂, t₁ ∪ t₂, _, _, _⟩,
    -- glueing together but minus overlap
    sorry, sorry, sorry }
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

end finite

section possibly_infinite

lemma to_fd (e : E) : ∃ (E' : subspace ℝ E) [finite_dimensional ℝ E'], e ∈ E' :=
begin
  classical,
  refine ⟨submodule.span ℝ (finset.image (basis.of_vector_space ℝ E)
    ((basis.of_vector_space ℝ E).repr e).support), _, _⟩,
  { apply finite_dimensional.span_finset,},
  { conv_lhs { rw ←(basis.of_vector_space ℝ E).total_repr e },
    rw finsupp.total_apply,
    convert submodule.sum_mem _ _,
    intros c hc,
    convert submodule.smul_mem _ _ _,
    apply submodule.subset_span,
    rw [finset.coe_image, set.mem_image],
    exact ⟨_, hc, rfl⟩},
end

@[simps] def tensor_submodule (E' : subspace ℝ E) (F' : subspace ℝ F) :
  (E' ⊗[ℝ] F') →ₗ[ℝ] (E ⊗[ℝ] F) :=
tensor_product.lift
{ to_fun := λ e',
  { to_fun := λ f', (e' : E) ⊗ₜ (f' : F),
    map_add' := λ f f', by rw [submodule.coe_add, tensor_product.tmul_add],
    map_smul' := λ r f, by rw [ring_hom.id_apply, submodule.coe_smul, tensor_product.tmul_smul], },
  map_add' := λ e e', linear_map.ext $ λ f, by rw [linear_map.coe_mk, submodule.coe_add,
    tensor_product.add_tmul, linear_map.add_apply, linear_map.coe_mk, linear_map.coe_mk],
  map_smul' := λ r e, linear_map.ext $ λ f, by rw [ring_hom.id_apply, linear_map.smul_apply,
    linear_map.coe_mk, linear_map.coe_mk, submodule.coe_smul, tensor_product.smul_tmul,
    tensor_product.tmul_smul] }

lemma tensor_submodule_mk {E' : subspace ℝ E} {F' : subspace ℝ F} (e : E') (f : F') :
  tensor_submodule E F E' F' (e ⊗ₜ f) = (e : E) ⊗ₜ (f : F) := rfl

lemma tensor_submodule_range_mono1 {E' E'' : subspace ℝ E} (F' : subspace ℝ F)
  (le1 : E' ≤ E'') :
  linear_map.range (tensor_submodule E F E' F') ≤
  linear_map.range (tensor_submodule E F E'' F') := λ x hx,
begin
  obtain ⟨x, rfl⟩ := hx,
  induction x using tensor_product.induction_on with e f x₁ x₂ ih₁ ih₂,
  { rw [map_zero], exact submodule.zero_mem _ },
  { rw [tensor_submodule_mk], exact ⟨⟨e, le1 e.2⟩ ⊗ₜ f, rfl⟩, },
  { rw [map_add], exact submodule.add_mem _ ih₁ ih₂, },
end

lemma tensor_submodule_range_mono2 (E' : subspace ℝ E) {F' F'' : subspace ℝ F}
  (le2 : F' ≤ F'') :
  linear_map.range (tensor_submodule E F E' F') ≤
  linear_map.range (tensor_submodule E F E' F'') := λ x hx,
begin
  obtain ⟨x, rfl⟩ := hx,
  induction x using tensor_product.induction_on with e f x₁ x₂ ih₁ ih₂,
  { rw [map_zero], exact submodule.zero_mem _ },
  { rw [tensor_submodule_mk], exact ⟨e ⊗ₜ ⟨f, le2 f.2⟩, rfl⟩, },
  { rw [map_add], exact submodule.add_mem _ ih₁ ih₂, },
end

lemma tensor_submodule_apply_tmul (E' : subspace ℝ E) (F' : subspace ℝ F) (e : E') (f : F') :
  tensor_submodule E F E' F' (e ⊗ₜ f) = (e : E) ⊗ₜ (f : F) := rfl

lemma to_tensor_fd (z : E ⊗[ℝ] F) : ∃ (E' : subspace ℝ E) (F' : subspace ℝ F)
  [finite_dimensional ℝ E'] [finite_dimensional ℝ F'],
  z ∈ (tensor_submodule E F E' F').range :=
begin
  induction z using tensor_product.induction_on with e f z₁ z₂ ih₁ ih₂,
  { refine ⟨⊥, ⊥, _, _, submodule.zero_mem _⟩,
    exacts [finite_dimensional_bot ℝ E, finite_dimensional_bot ℝ F] },
  { rcases to_fd E e with ⟨E', iE', he⟩,
    rcases to_fd F f with ⟨F', iF', hf⟩,
    exact ⟨E', F', iE', iF', ⟨⟨e, he⟩ ⊗ₜ ⟨f, hf⟩, rfl⟩⟩, },
  { rcases ih₁ with ⟨E1, F1, iE1, iF1, ⟨z1, rfl⟩⟩,
    rcases ih₂ with ⟨E2, F2, iE2, iF2, ⟨z2, rfl⟩⟩,
    resetI,
    have le1 : linear_map.range (tensor_submodule E F E1 F1) ≤
      linear_map.range (tensor_submodule E F (E1 ⊔ E2) (F1 ⊔ F2)),
    { exact (tensor_submodule_range_mono1 E F F1 (le_sup_left : E1 ≤ E1 ⊔ E2)).trans
        (tensor_submodule_range_mono2 E F _ _), },
    have le2 : linear_map.range (tensor_submodule E F E2 F2) ≤
      linear_map.range (tensor_submodule E F (E1 ⊔ E2) (F1 ⊔ F2)),
    { exact (tensor_submodule_range_mono1 _ _ _ (le_sup_right : E2 ≤ E1 ⊔ E2)).trans
        (tensor_submodule_range_mono2 _ _ _ _), },
    exact ⟨E1 ⊔ E2, F1 ⊔ F2, submodule.finite_dimensional_sup E1 E2,
      submodule.finite_dimensional_sup F1 F2, submodule.add_mem _ (le1 ⟨z1, rfl⟩) (le2 ⟨z2, rfl⟩)⟩ },
end

lemma tensor_product_aux_restrict_apply' (x y : E ⊗[ℝ] F)
  (E' : subspace ℝ E) (F' : subspace ℝ F) (x' y' : E' ⊗[ℝ] F')
  (hx : x = tensor_submodule E F E' F' x')
  (hy : y = tensor_submodule E F E' F' y') :
  (tensor_product_aux E F (x ⊗ₜ y)) =
  (tensor_product_aux E' F' (x' ⊗ₜ y')) :=
begin
  rw [hx, hy], revert x,
  induction x' using tensor_product.induction_on with e' f' x₁ x₂ ih₁ ih₂,
  { simp only [map_zero, tensor_product.zero_tmul], exact λ _ _, rfl, },
  { rw [tensor_submodule_apply_tmul], revert y,
    induction y' using tensor_product.induction_on with e'' f'' y₁ y₂ ih₁ ih₂,
    { simp only [map_zero, tensor_product.tmul_zero], exact λ _ _ _ _, rfl, },
    { intros x h y h', simpa only [tensor_submodule_apply_tmul, tensor_product_aux_apply], },
    { intros x hx y hy,
      rw [map_add, tensor_product.tmul_add, map_add, tensor_product.tmul_add,
        map_add, ih₁, ih₂], refl, refl, refl, refl, }, },
  { intros x hx,
    simp only [tensor_product.add_tmul, map_add],
    rw [ih₁, ih₂], refl, refl, },
end

lemma tensor_product_aux_restrict_apply (x y : E ⊗[ℝ] F)
  (E' : subspace ℝ E) (F' : subspace ℝ F)
  (hx : x ∈ (tensor_submodule E F E' F').range)
  (hy : y ∈ (tensor_submodule E F E' F').range) :
  (tensor_product_aux E F (x ⊗ₜ y)) =
  (tensor_product_aux E' F' (hx.some ⊗ₜ hy.some)) :=
begin
  apply tensor_product_aux_restrict_apply',
  exacts [hx.some_spec.symm, hy.some_spec.symm],
end

instance tensor_product' : inner_product_space ℝ (E ⊗[ℝ] F) :=
of_core
{ inner := λ x y, tensor_product_aux E F (x ⊗ₜ y),
  conj_sym := sorry,
  nonneg_re := begin
    intros z, rw is_R_or_C.re_to_real,
    obtain ⟨E', F', iE', iF', hz⟩ := to_tensor_fd E F z,
    rw tensor_product_aux_restrict_apply E F z z E' F'
      hz hz,
    resetI,
    convert_to 0 ≤ (inner_product_space.tensor_product_of_finite E' F').inner _ _,
    exact real_inner_self_nonneg,
  end,
  definite := sorry,
  add_left := sorry,
  smul_left := sorry }

end possibly_infinite

end inner_product_space
