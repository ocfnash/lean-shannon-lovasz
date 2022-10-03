import to_mathlib.analysis.inner_product_space.tensor_product
import to_mathlib.linear_algebra.tensor_power

noncomputable theory

open set function tensor_power
open_locale tensor_product big_operators real_inner_product_space

namespace inner_product_space

namespace tensor_power

variables (E : Type*) [inner_product_space ℝ E]

def linear_equiv.map_eq_zero {R M N : Type*} [add_comm_group M] [add_comm_group N]
  [comm_ring R] [module R M] [module R N] (l : M ≃ₗ[R] N) (x : M) :
  l x = 0 ↔ x = 0 :=
(show l x = 0 ↔ x ∈ linear_map.ker l, by rw linear_map.mem_ker).trans begin
  suffices : linear_map.ker l = ⊥,
  { rw this, refl },
  exact (linear_map.ker_eq_bot.mpr l.injective : linear_map.ker l.to_linear_map = ⊥),
end

def lift_equiv_left {M N N' R : Type*} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid N']
  [comm_semiring R] [module R M] [module R N] [module R N'] (l : N ≃ₗ[R] N') :
  M ⊗[R] N ≃ₗ[R] M ⊗[R] N' :=
{ to_fun := tensor_product.hom_tensor_hom_map R M N M N' (linear_map.id ⊗ₜ[R] l),
  map_add' := map_add _,
  map_smul' := map_smul _,
  inv_fun := tensor_product.hom_tensor_hom_map R M N' M N (linear_map.id ⊗ₜ[R] l.symm),
  left_inv := λ r, begin
    induction r using tensor_product.induction_on with x y x y ihx ihy,
    { simp only [map_zero] },
    { rw [tensor_product.hom_tensor_hom_map_apply, tensor_product.hom_tensor_hom_map_apply],
      simp only [tensor_product.map_tmul, linear_map.id_coe, id.def, linear_equiv.coe_coe,
        linear_equiv.symm_apply_apply], },
    { simp only [map_add, ihx, ihy] },
  end,
  right_inv := λ x, begin
    induction x using tensor_product.induction_on with x y x y ihx ihy,
    { simp only [map_zero] },
    { rw [tensor_product.hom_tensor_hom_map_apply, tensor_product.hom_tensor_hom_map_apply],
      simp only [tensor_product.map_tmul, linear_map.id_coe, id.def, linear_equiv.coe_coe,
        linear_equiv.apply_symm_apply], },
    { simp only [map_add, ihx, ihy] },
  end }

lemma lift_equiv_left_tmul {M N N' R : Type*} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid N']
  [comm_semiring R] [module R M] [module R N] [module R N'] (l : N ≃ₗ[R] N')
  (m : M) (n : N) : lift_equiv_left l (m ⊗ₜ n) = m ⊗ₜ (l n) := rfl

def core_zero_power : inner_product_space.core ℝ (⨂[ℝ]^0 E) :=
{ inner := λ x y, (pi_tensor_product.is_empty_equiv (fin 0) x) *
    (pi_tensor_product.is_empty_equiv (fin 0) y),
  conj_sym := λ x y, by rw [is_R_or_C.conj_to_real, mul_comm],
  nonneg_re := λ x, by simpa only [is_R_or_C.re_to_real] using mul_self_nonneg _,
  definite := λ x hx,
  begin
    rw mul_self_eq_zero at hx,
    have hx' : x ∈ linear_map.ker (pi_tensor_product.is_empty_equiv (fin 0) : ⨂[ℝ]^0 E ≃ₗ[ℝ] ℝ),
    { rwa linear_map.mem_ker, },
    have h' := linear_map.ker_eq_bot.mpr
      ((pi_tensor_product.is_empty_equiv (fin 0) : ⨂[ℝ]^0 E ≃ₗ[ℝ] ℝ).injective),
    erw h' at hx',
    exact hx',
  end,
  add_left := λ x y z, by simp only [map_add, add_mul],
  smul_left := λ x y r, by simp only [map_smul, smul_eq_mul, is_R_or_C.conj_to_real, mul_assoc] }

lemma core_zero_power_inner_apply (e₁ e₂ : fin 0 → E) :
  (core_zero_power E).inner (tpow ℝ e₁) (tpow ℝ e₂) =
  ∏ i : fin 0, ⟪e₁ i, e₂ i⟫ :=
begin
  rw [fin.prod_univ_zero],
  dunfold core_zero_power, dsimp only,
  erw [pi_tensor_product.is_empty_equiv_apply_tprod, mul_one],
end

def core_succ_power {k : ℕ} (ic : inner_product_space.core ℝ (⨂[ℝ]^k E)) :
  inner_product_space.core ℝ (⨂[ℝ]^k.succ E) :=
let l : ⨂[ℝ]^k.succ E ≃ₗ[ℝ] ⨂[ℝ]^k E ⊗[ℝ] E :=
  (@tensor_power.mul_equiv ℝ E _ _ _ k 1).symm.trans
  (lift_equiv_left (pi_tensor_product.subsingleton_equiv 0) : ⨂[ℝ]^k E ⊗ ⨂[ℝ]^1 E ≃ₗ[ℝ] ⨂[ℝ]^k E ⊗[ℝ] E),
  inner_product_space' : inner_product_space ℝ (⨂[ℝ]^k E ⊗[ℝ] E) :=
    @inner_product_space.tensor_product' (⨂[ℝ]^k E) E (inner_product_space.of_core ic) _,
  i : (⨂[ℝ]^k E ⊗[ℝ] E) → (⨂[ℝ]^k E ⊗[ℝ] E) → ℝ := inner_product_space'.inner in
{ inner := λ x y, i (l x) (l y),
  conj_sym := λ x y, begin
    convert inner_conj_sym (l x) (l y),
  end,
  nonneg_re := λ x, begin
    convert inner_product_space.core.nonneg_re _ (l x),
  end,
  definite := λ x hx, begin
    have := inner_product_space.core.definite _ (l x) hx,
    rwa linear_equiv.map_eq_zero l x at this,
  end,
  add_left := λ x y z, begin
    convert inner_product_space.core.add_left _ (l x) (l y) (l z),
    rw map_add,
  end,
  smul_left := λ x y r, begin
    convert inner_product_space.core.smul_left _ (l x) (l y) r,
    rw map_smul,
  end }

lemma core_succ_power_inner_apply_aux {k : ℕ} (e₁ e₂ : fin k.succ → E)
  (ic : inner_product_space.core ℝ (⨂[ℝ]^k E)) :
  (core_succ_power E ic).inner (tpow ℝ e₁) (tpow ℝ e₂) =
  (@inner_product_space.tensor_product' (⨂[ℝ]^k E) E
    (inner_product_space.of_core ic) _).inner
      ((@tensor_power.mul_equiv ℝ E _ _ _ k 1).symm.trans
  (lift_equiv_left (pi_tensor_product.subsingleton_equiv 0) : ⨂[ℝ]^k E ⊗ ⨂[ℝ]^1 E ≃ₗ[ℝ] ⨂[ℝ]^k E ⊗[ℝ] E) (tpow ℝ e₁))
  ((@tensor_power.mul_equiv ℝ E _ _ _ k 1).symm.trans
  (lift_equiv_left (pi_tensor_product.subsingleton_equiv 0) : ⨂[ℝ]^k E ⊗ ⨂[ℝ]^1 E ≃ₗ[ℝ] ⨂[ℝ]^k E ⊗[ℝ] E) (tpow ℝ e₂)) :=
rfl

def core (k : ℕ) : inner_product_space.core ℝ (⨂[ℝ]^k E) :=
nat.rec (core_zero_power E) (λ n hn, core_succ_power E hn) k

lemma core_succ_power_inner_apply_tpow {k : ℕ} (e₁ e₂ : fin k.succ → E) :
  (core_succ_power E (core E k)).inner (tpow ℝ e₁) (tpow ℝ e₂) =
  (core E k).inner
    (tpow ℝ (λ (i : fin k), e₁ (@fin_sum_fin_equiv k 1 (sum.inl i))))
    (tpow ℝ (λ (i : fin k), e₂ (@fin_sum_fin_equiv k 1 (sum.inl i)))) *
  ⟪e₁ ⟨k, lt_add_one _⟩, e₂ ⟨k, lt_add_one _⟩⟫ :=
begin
  simp only [core_succ_power_inner_apply_aux],
  dunfold tpow tensor_power.mul_equiv,
  simp only [linear_equiv.trans_symm, pi_tensor_product.reindex_symm, linear_equiv.trans_apply,
    pi_tensor_product.reindex_tprod, pi_tensor_product.tmul_equiv_symm_apply,
    lift_equiv_left_tmul, pi_tensor_product.subsingleton_equiv_apply_tprod],
  simp_rw [equiv.symm_symm],
  erw inner_product_space.inner_tprod,
  rw [fin_sum_fin_equiv_apply_right], congr,
end


lemma core_inner_tpow {k : ℕ} (e₁ e₂ : fin k → E) :
  (core E k).inner (tpow ℝ e₁) (tpow ℝ e₂) =
  ∏ i, ⟪e₁ i, e₂ i⟫ :=
begin
  induction k with k ih,
  { apply core_zero_power_inner_apply, },
  { erw [core_succ_power_inner_apply_tpow E e₁ e₂, ih, fin.prod_univ_succ_above, mul_comm],
    congr' 1,
    apply finset.prod_congr rfl,
    rintros ⟨x, hx⟩ -,
    congr' 2;
    { simp only [fin_sum_fin_equiv_apply_left, fin.cast_add_mk],
      ext, simp only [fin.coe_mk],
      rw fin.succ_above_below, refl, assumption, },
     }
end

instance (k : ℕ) : inner_product_space ℝ (⨂[ℝ]^k E) :=
inner_product_space.of_core (core E k)

@[simp] lemma inner_tpow {k : ℕ} (e₁ e₂ : fin k → E) :
  ⟪tensor_power.tpow ℝ e₁, tensor_power.tpow ℝ e₂⟫ = ∏ i, ⟪e₁ i, e₂ i⟫ :=
core_inner_tpow E e₁ e₂

end tensor_power

end inner_product_space
