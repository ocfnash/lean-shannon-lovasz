import to_mathlib.analysis.inner_product_space.tensor_product
import analysis.inner_product_space.gram_schmidt_ortho
import data.fin.basic

noncomputable theory

open_locale real_inner_product_space tensor_product big_operators

namespace inner_product_space

variables (E F : Type*) [linear_order E] [linear_order F]
variables [inner_product_space ℝ E] [inner_product_space ℝ F]

section finite

variables [finite_dimensional ℝ E] [finite_dimensional ℝ F]

#check basis (fin (finite_dimensional.finrank ℝ E) × fin (finite_dimensional.finrank ℝ F)) ℝ
 (E ⊗[ℝ] F)
#check (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E))

@[reducible] def canonical_basis_repr_aux (e : E) (f : F) : fin (finite_dimensional.finrank ℝ E) × fin (finite_dimensional.finrank ℝ F) →₀ ℝ :=
{ support := ((gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E)).to_basis.repr e).support ×ˢ
    ((gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F)).to_basis.repr f).support ,
  to_fun := λ i, (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E)).to_basis.coord i.1 e *
    (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F)).to_basis.coord i.2 f,
  mem_support_to_fun := λ ⟨i, j⟩, begin
    split; intros h;
    simp only [basis.coord_apply, orthonormal_basis.coe_to_basis_repr_apply, ne.def, mul_eq_zero, finset.mem_product,
      finsupp.mem_support_iff] at h ⊢,
    { tauto, }, { tauto },
  end }

@[simps] def canonical_basis_repr :
  E ⊗[ℝ] F →ₗ[ℝ] fin (finite_dimensional.finrank ℝ E) × fin (finite_dimensional.finrank ℝ F) →₀ ℝ :=
tensor_product.lift
{ to_fun := λ e,
  { to_fun := λ f, canonical_basis_repr_aux E F e f,
    map_add' := λ x y, by { ext1, simp only [finsupp.coe_mk, finsupp.add_apply, map_add, mul_add] },
    map_smul' := λ r f, begin
      ext1, simp only [finsupp.coe_mk, ring_hom.id_apply, finsupp.coe_smul, map_smul, pi.smul_apply,
        smul_eq_mul], ring1,
    end },
  map_add' := λ e e', begin
    ext : 2, simp only [linear_map.coe_mk, finsupp.coe_mk, map_add, add_mul, linear_map.add_apply,
      finsupp.add_apply],
  end,
  map_smul' := λ r e, begin
    ext : 2, simp only [linear_map.coe_mk, finsupp.coe_mk, finsupp.coe_smul, ring_hom.id_apply,
      linear_map.smul_apply, map_smul, pi.smul_apply, smul_eq_mul], ring1,
  end }

lemma canonical_basis_repr_tmul (e) (f) (x) :
  canonical_basis_repr E F (e ⊗ₜ f) x =
  (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E)).to_basis.coord x.1 e *
  (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F)).to_basis.coord x.2 f :=
by simp only [canonical_basis_repr_apply, tensor_product.lift_aux_tmul, linear_map.coe_mk,
    finsupp.coe_mk]

@[reducible] def canonical_basis_repr_symm :
  (fin (finite_dimensional.finrank ℝ E) × fin (finite_dimensional.finrank ℝ F) →₀ ℝ) →ₗ[ℝ] E ⊗[ℝ] F :=
finsupp.lsum ℝ $ λ (i : fin (finite_dimensional.finrank ℝ E) × fin (finite_dimensional.finrank ℝ F)),
({ to_fun := λ μ, μ • (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E) i.1 ⊗ₜ[ℝ]
    gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F) i.2),
  map_add' := λ r s, add_smul _ _ _,
  map_smul' := λ r x, mul_smul _ _ _ } : ℝ →ₗ[ℝ] E ⊗ F)

lemma canonical_basis_repr_apply_symm_apply :
  (canonical_basis_repr E F).comp (canonical_basis_repr_symm E F) = linear_map.id :=
begin
  ext z a, rw [linear_map.id_comp, linear_map.comp_apply, linear_map.comp_apply,
    finsupp.lsingle_apply, finsupp.lsum_single, linear_map.coe_mk, one_smul, finsupp.single_apply,
    canonical_basis_repr_tmul],
  split_ifs,
  { subst h,
    simp only [basis.coord_apply, orthonormal_basis.coe_to_basis_repr_apply, orthonormal_basis.repr_self,
      euclidean_space.single_apply, eq_self_iff_true, if_true, mul_one], },
  { simp only [basis.coord_apply, orthonormal_basis.coe_to_basis_repr_apply, orthonormal_basis.repr_self,
  euclidean_space.single_apply, boole_mul, ite_eq_right_iff, one_ne_zero],
    intros eq1 eq2, refine h _, ext, rw eq1.symm, rw eq2.symm, },
end

lemma canonical_basis_repr_symm_apply_apply_on_basis (i j) :
  canonical_basis_repr_symm E F (canonical_basis_repr E F $
    (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E)).to_basis i ⊗ₜ
    (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F)).to_basis j) =
  (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E)).to_basis i ⊗ₜ
  (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F)).to_basis j :=
begin
  rw [finsupp.lsum_apply, finsupp.sum],
  simp_rw [linear_map.coe_mk, canonical_basis_repr_tmul,
    basis.coord_apply],
  have seq : (canonical_basis_repr E F $
    (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E)).to_basis i ⊗ₜ
    (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F)).to_basis j).support =
  ({i} : finset _).product ({j}),
  { ext, split; intros h;
    simp only [finset.product_singleton, finset.map_singleton, function.embedding.coe_fn_mk,
      finset.mem_singleton, canonical_basis_repr_tmul, finsupp.mem_support_iff] at h ⊢,
    { rw [mul_ne_zero_iff, basis.coord_apply, basis.coord_apply] at h,
      rw [basis.repr_self, basis.repr_self, finsupp.single_apply, finsupp.single_apply] at h,
      rw prod.ext_iff, split_ifs at h with h1 h2, exact ⟨h1.symm, h2.symm⟩,
      exact false.elim (h.2 rfl), exact false.elim (h.1 rfl), exact false.elim (h.1 rfl), },
    { rw prod.ext_iff at h, rw [mul_ne_zero_iff, basis.coord_apply, basis.coord_apply,
        basis.repr_self, basis.repr_self, finsupp.single_apply, finsupp.single_apply,
        if_pos h.1.symm, if_pos h.2.symm], split; norm_num, }, },
    simp_rw seq, rw [finset.singleton_product_singleton, finset.sum_singleton],
    dsimp only, rw [basis.repr_self, basis.repr_self, finsupp.single_apply, finsupp.single_apply,
      if_pos rfl, if_pos rfl, one_mul, one_smul, orthonormal_basis.coe_to_basis,
      orthonormal_basis.coe_to_basis],
end

lemma canonical_basis_repr_symm_apply_apply :
  (canonical_basis_repr_symm E F).comp (canonical_basis_repr E F) = linear_map.id :=
begin
  apply tensor_product.algebra_tensor_module.ext, intros e f,
  conv_lhs { rw [←(gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E)).to_basis.total_repr e,
    ←(gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F)).to_basis.total_repr f] },
  rw [finsupp.total_apply, finsupp.total_apply, finsupp.sum, finsupp.sum, linear_map.id_apply,
    sum_tensor_sum, linear_map.comp_apply, map_sum, map_sum],
  simp_rw [tensor_product.tmul_smul, tensor_product.smul_tmul, tensor_product.tmul_smul, ←mul_smul,
    map_smul, canonical_basis_repr_symm_apply_apply_on_basis],
  conv_rhs { rw [←(gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E)).to_basis.total_repr e,
    ←(gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F)).to_basis.total_repr f] },
  rw [finsupp.total_apply, finsupp.total_apply, finsupp.sum, finsupp.sum, sum_tensor_sum],
  rw finset.sum_congr rfl,
  rintros ⟨i, j⟩ h, dsimp only,
  rw [tensor_product.tmul_smul, tensor_product.smul_tmul, tensor_product.tmul_smul, ←mul_smul],
end

lemma canonical_basis_repr_surj : function.surjective (canonical_basis_repr E F) :=
λ x, ⟨canonical_basis_repr_symm E F x, fun_like.congr_fun
  (canonical_basis_repr_apply_symm_apply E F) x⟩

def finsupp.from_tensor : ((fin (finite_dimensional.finrank ℝ E) →₀ ℝ) ⊗[ℝ] (fin (finite_dimensional.finrank ℝ F) →₀ ℝ))
  →ₗ[ℝ] (fin (finite_dimensional.finrank ℝ E) × fin (finite_dimensional.finrank ℝ F) →₀ ℝ) :=
tensor_product.lift
{ to_fun := λ e,
  { to_fun := λ f, (⟨e.support ×ˢ f.support, λ i, e i.1 * f i.2, begin
      rintros ⟨i, j⟩, simp only [finset.mem_product, finsupp.mem_support_iff, ne.def, mul_eq_zero], tauto,
    end⟩ : fin (finite_dimensional.finrank ℝ E) × fin (finite_dimensional.finrank ℝ F) →₀ ℝ),
    map_add' := λ x y, begin
      ext1 ⟨i, j⟩, rw [finsupp.coe_mk, finsupp.add_apply, finsupp.add_apply, finsupp.coe_mk, finsupp.coe_mk, mul_add],
    end,
    map_smul' := λ r s, begin
      ext1 ⟨i, j⟩, rw [finsupp.coe_mk, finsupp.smul_apply, ring_hom.id_apply, finsupp.coe_smul, pi.smul_apply,
        finsupp.coe_mk, smul_eq_mul, smul_eq_mul], ring1,
    end },
  map_add' := λ x y, begin
    ext k ⟨i, j⟩, simp only [linear_map.comp_apply, linear_map.coe_mk, finsupp.coe_mk, linear_map.add_apply, finsupp.add_apply,
      finsupp.lsingle_apply], ring1,
  end,
  map_smul' := λ r x, begin
    ext k ⟨i, j⟩, simp only [linear_map.comp_apply, linear_map.coe_mk, finsupp.coe_mk, linear_map.add_apply, finsupp.add_apply,
      finsupp.lsingle_apply, finsupp.coe_smul, finsupp.smul_apply, pi.smul_apply, ring_hom.id_apply,
      linear_map.smul_apply, smul_eq_mul], ring1,
  end }

lemma canonical_basis_repr_inj : function.injective (canonical_basis_repr E F) :=
begin
  intros x y h,
  apply_fun canonical_basis_repr_symm E F at h,
  erw [fun_like.congr_fun (canonical_basis_repr_symm_apply_apply E F) x,
    fun_like.congr_fun (canonical_basis_repr_symm_apply_apply E F) y] at h,
  exact h,
end

@[simps] def canonical_basis :
  basis (fin (finite_dimensional.finrank ℝ E) × fin (finite_dimensional.finrank ℝ F)) ℝ
 (E ⊗[ℝ] F) :=
⟨{ ..canonical_basis_repr E F,
  ..equiv.of_bijective _ ⟨canonical_basis_repr_inj E F, canonical_basis_repr_surj E F⟩}⟩

lemma canonical_basis_apply (x) :
  (canonical_basis E F x) =
  (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E)) x.1 ⊗ₜ
  (gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F)) x.2 :=
begin
  change (canonical_basis E F).repr.symm _ = _,
  apply_fun (canonical_basis E F).repr using canonical_basis_repr_inj,
  ext i,
  erw canonical_basis_repr_tmul,
  erw linear_equiv.apply_symm_apply,
  rw finsupp.single_apply,
  simp only [orthonormal_basis.coe_to_basis, basis.coord_apply, orthonormal_basis.coe_to_basis_repr_apply,
    orthonormal_basis.repr_self, euclidean_space.single_apply, boole_mul],
  simp_rw [prod.ext_iff, ite_and], split_ifs; tauto,
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
    rw [←(canonical_basis E F).total_repr z, finsupp.total_apply, finsupp.sum,
      sum_tensor_sum, map_sum],
    simp_rw [tensor_product.smul_tmul, tensor_product.tmul_smul, map_smul, ←mul_smul,
      canonical_basis_apply, tensor_product_aux_apply, orthonormal_iff_ite.mp onb_E.orthonormal,
      orthonormal_iff_ite.mp onb_F.orthonormal, ite_mul, one_mul, zero_mul, smul_ite, smul_eq_mul,
      mul_one, mul_zero],
    rw [←finset.sum_filter, ←finset.sum_filter],
    apply finset.sum_nonneg,
    rintros ⟨⟨a, b⟩, ⟨c, d⟩⟩ h,
    simp only [finset.mem_filter, finset.mem_product] at h,
    dsimp only, rw [h.1.2, h.2],
    exact mul_self_nonneg _,
  end,
  definite := λ z hz, begin
    classical,
    set onb_E := gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ E),
    set onb_F := gram_schmidt_orthonormal_basis ℝ (finite_dimensional.fin_basis ℝ F),
    rw [←(canonical_basis E F).total_repr z, finsupp.total_apply, finsupp.sum,
      sum_tensor_sum, map_sum] at hz,
    simp_rw [tensor_product.smul_tmul, tensor_product.tmul_smul, map_smul, ←mul_smul,
      canonical_basis_apply, tensor_product_aux_apply, orthonormal_iff_ite.mp onb_E.orthonormal,
      orthonormal_iff_ite.mp onb_F.orthonormal, ite_mul, one_mul, zero_mul, smul_ite, smul_eq_mul,
      mul_one, mul_zero] at hz,
    rw [←finset.sum_filter, ←finset.sum_filter, finset.sum_eq_zero_iff_of_nonneg] at hz,
    work_on_goal 2
    { rintros ⟨⟨a, b⟩, ⟨c, d⟩⟩ h,
      simp only [finset.mem_filter, finset.mem_product] at h,
      dsimp only, rw [h.1.2, h.2],
      exact mul_self_nonneg _, },
    rw [←(canonical_basis E F).total_repr z, finsupp.total_apply, finsupp.sum],
    apply finset.sum_eq_zero,
    intros x hx, specialize hz (x, x),
    rw [finset.mem_filter, finset.mem_filter, finset.mem_product] at hz,
    specialize hz ⟨⟨⟨hx, hx⟩, rfl⟩, rfl⟩,
    rw [mul_self_eq_zero] at hz, rw [hz, zero_smul],
  end,
  add_left := λ x y z, by rw [tensor_product.add_tmul, map_add],
  smul_left := λ x y r, by rw [is_R_or_C.conj_to_real,
    ← tensor_product.smul_tmul', map_smul, smul_eq_mul] }

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
        (tensor_submodule_range_mono2 E F _ le_sup_left), },
    have le2 : linear_map.range (tensor_submodule E F E2 F2) ≤
      linear_map.range (tensor_submodule E F (E1 ⊔ E2) (F1 ⊔ F2)),
    { exact (tensor_submodule_range_mono1 _ _ _ (le_sup_right : E2 ≤ E1 ⊔ E2)).trans
        (tensor_submodule_range_mono2 _ _ _ le_sup_right), },
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
    intros z, rw is_R_or_C.re_to_real,
    obtain ⟨E', F', iE', iF', hz⟩ := to_tensor_fd E F z,
    rw tensor_product_aux_restrict_apply E F z z E' F'
      hz hz,
    resetI,
    convert_to 0 ≤ (inner_product_space.tensor_product_of_finite E' F').inner _ _,
    exact real_inner_self_nonneg,
  end,
  definite := begin
    intros z h,
    obtain ⟨E', F', iE', iF', hz⟩ := to_tensor_fd E F z,
    rw tensor_product_aux_restrict_apply E F z z E' F'
      hz hz at h,
    resetI,
    change (inner_product_space.tensor_product_of_finite E' F').inner hz.some hz.some = (0 : ℝ) at h,
    have h' : hz.some = 0 := inner_product_space.core.definite _ _ h,
    have h'' := hz.some_spec,
    rw [h', map_zero] at h'', exact h''.symm,
  end,
  add_left := λ x y z, by rw [tensor_product.add_tmul, map_add],
  smul_left := λ x y r, by rw [is_R_or_C.conj_to_real,
    ← tensor_product.smul_tmul', map_smul, smul_eq_mul] }

@[simp] lemma inner_tprod (e₁ e₂ : E) (f₁ f₂ : F) :
  ⟪e₁ ⊗ₜ[ℝ] f₁, e₂ ⊗ₜ[ℝ] f₂⟫ = ⟪e₁, e₂⟫ * ⟪f₁, f₂⟫ :=
tensor_product_aux_apply E F e₁ e₂ f₁ f₂

end possibly_infinite

end inner_product_space
