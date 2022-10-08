import linear_algebra.tensor_power
import analysis.inner_product_space.pi_L2
import to_mathlib.analysis.inner_product_space.tensor_product
import to_mathlib.analysis.inner_product_space.tensor_power
import to_mathlib.combinatorics.simple_graph.strong_product
import to_mathlib.combinatorics.simple_graph.independent
import algebra.order.field
import algebra.order.monoid
import topology.algebra.order.basic

noncomputable theory

open set function
open_locale real_inner_product_space tensor_product big_operators pointwise

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
   norm_eq_one' := λ v, begin
    rw [norm_eq_sqrt_real_inner, real.sqrt_eq_iff_mul_self_eq, one_mul,
      euclidean_space.inner_single_left, map_one, one_mul, euclidean_space.single_apply, if_pos rfl],
    exact real_inner_self_nonneg, norm_num,
   end,
   inner_eq_zero_of_ne_of_not_adj' := λ v w h nadj, begin
    rw [euclidean_space.inner_single_left, map_one, one_mul, euclidean_space.single_apply, if_neg h],
   end, }⟩

variables {G E} (ρ : orthogonal_representation G E)

@[simp] lemma norm_eq_one {v : V} : ∥ρ v∥ = 1 :=
ρ.norm_eq_one' v

@[simp] lemma inner_self_eq_one (v : V) : inner (ρ v) (ρ v) = (1 : ℝ) :=
begin
  have : ∥ρ v∥ = 1 := ρ.norm_eq_one,
  rw [norm_eq_sqrt_inner, real.sqrt_eq_iff_mul_self_eq, mul_one, is_R_or_C.re_to_real] at this,
  exact this.symm, exact real_inner_self_nonneg, norm_num,
end

lemma inner_eq_zero_of_ne_of_not_adj {v w : V} (h₁ : v ≠ w) (h₂ : ¬ G.adj v w) :
  ⟪ρ v, ρ w⟫ = 0 :=
ρ.inner_eq_zero_of_ne_of_not_adj' v w h₁ h₂

lemma orthormal_on_independent (I : set V) (hI : G.independent_set I) :
  orthonormal ℝ (I.restrict ρ) :=
⟨λ _, ρ.norm_eq_one, λ i j h, ρ.inner_eq_zero_of_ne_of_not_adj (λ r, h $ subtype.ext r) $ hI i j⟩

/-- The Lovász number of an orthogonal representation of a graph at a vector `e`. -/
def lovasz_number_at (e : E) : ℝ :=
⨆ v, ∥e∥^2 / ⟪ρ v, e⟫^2

@[simp] lemma lovasz_number_at_nneg (e : E) :
  0 ≤ ρ.lovasz_number_at e :=
  begin
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

lemma independence_number_le_lovasz_number_at [fintype V] (e : E) :
  (G.independence_number : ℝ) ≤ ρ.lovasz_number_at e :=
sorry

variables {W F : Type*} {H : simple_graph W}
variables [inner_product_space ℝ F] (ρ' : orthogonal_representation H F)

/-- If `ρ` is an orthogonal representation of a graph `G` in `E` and `ρ'` is an orthogonal
representation of a graph `H` in `F`, then `(x, y) ↦ (ρ x) ⊗ₜ (ρ' y)` defines an orthogonal
representation of the graph `G.strong_prod H` on `E ⊗ F`.

Actually we probably won't need this definition for this project but it might be good practice
to fill in the proofs below. -/
@[simps] def prod : orthogonal_representation (G.strong_prod H) (E ⊗[ℝ] F) :=
{ to_fun := λ x, (ρ x.1) ⊗ₜ (ρ' x.2),
  norm_eq_one' := λ ⟨v, w⟩, begin
    rw [norm_eq_sqrt_real_inner, real.sqrt_eq_iff_mul_self_eq, one_mul,
      inner_product_space.inner_tprod, ρ.inner_self_eq_one, one_mul,
      ρ'.inner_self_eq_one],
    exact real_inner_self_nonneg, norm_num,
  end,
  inner_eq_zero_of_ne_of_not_adj' := λ ⟨v, w⟩ ⟨v', w'⟩ neq nadj,
  begin
    rw [simple_graph.strong_prod_adj, not_and_distrib, not_not, not_and_distrib,
      not_or_distrib, not_or_distrib] at nadj,
    rw [inner_product_space.inner_tprod],
    dsimp only at nadj,
    rcases nadj with h|⟨h1, h2⟩|⟨h1, h2⟩,
    { exact false.elim (neq h) },
    { rw [ρ.inner_eq_zero_of_ne_of_not_adj h1 h2, zero_mul] },
    { rw [ρ'.inner_eq_zero_of_ne_of_not_adj h1 h2, mul_zero] },
  end, }

lemma real.Sup_mul_Sup
  (s : set ℝ) (hs : ∀ (a : ℝ), a ∈ s → 0 ≤ a)
  (t : set ℝ) (ht : ∀ (a : ℝ), a ∈ t → 0 ≤ a):
  Sup s * Sup t = Sup (s * t) :=
begin
  have le1 : 0 ≤ Sup s := real.Sup_nonneg _ hs,
  have le2 : 0 ≤ Sup t := real.Sup_nonneg _ ht,
  obtain rfl | hs1 := s.eq_empty_or_nonempty,
  { rw [real.Sup_empty, zero_mul, set.empty_mul, real.Sup_empty], },
  obtain rfl | ht1 := t.eq_empty_or_nonempty,
  { rw [real.Sup_empty, mul_zero, set.mul_empty, real.Sup_empty], },
  have hst1 : (s * t).nonempty := ⟨hs1.some * ht1.some, ⟨_, _, hs1.some_spec, ht1.some_spec, rfl⟩⟩,
  obtain rfl | hs0 := eq_or_ne s {0},
  { rw [cSup_singleton, zero_mul, show {(0 : ℝ)} * t = {0}, from _, cSup_singleton],
    ext1, split,
    { rintros ⟨x, y, hx, hy, rfl⟩,
      rw set.mem_singleton_iff at hx ⊢,
      rw [hx, zero_mul], },
    { rintros hx, rw set.mem_singleton_iff at hx, rw hx,
      exact ⟨0, ht1.some, set.mem_singleton _, ht1.some_spec, zero_mul _⟩, } },
  obtain rfl | ht0 := eq_or_ne t {0},
  { rw [cSup_singleton, mul_zero, show s * {(0 : ℝ)} = {0}, from _, cSup_singleton],
    ext1, split,
    { rintros ⟨x, y, hx, hy, rfl⟩,
      rw set.mem_singleton_iff at hy ⊢,
      rw [hy, mul_zero], },
    { rintros hx, rw set.mem_singleton_iff at hx, rw hx,
      exact ⟨hs1.some, 0, hs1.some_spec, set.mem_singleton _, mul_zero _⟩, } },
  replace hs0 : ∃ x : ℝ, x ∈ s ∧ x ≠ 0,
  { contrapose! hs0, rw eq_singleton_iff_nonempty_unique_mem,
    refine ⟨hs1, hs0⟩, },
  replace ht0 : ∃ x : ℝ, x ∈ t ∧ x ≠ 0,
  { contrapose! ht0, rw eq_singleton_iff_nonempty_unique_mem,
    refine ⟨ht1, ht0⟩, },
  by_cases hs2 : ¬bdd_above s,
  { rw [real.Sup_def s, dif_neg, zero_mul, real.Sup_def, dif_neg],
    rw [not_and_distrib], right, contrapose! hs2,
    rcases hs2 with ⟨M, hM⟩,
    refine ⟨M/ht0.some, λ x hx, _⟩,
    specialize hM ⟨x, ht0.some, hx, ht0.some_spec.1, rfl⟩,
    rwa le_div_iff, apply lt_of_le_of_ne, exact ht _ ht0.some_spec.1,
    exact ht0.some_spec.2.symm,
    rw [not_and_distrib], right, assumption, },
  by_cases ht2 : ¬bdd_above t,
  { rw [real.Sup_def t, dif_neg, mul_zero, real.Sup_def, dif_neg],
    rw [not_and_distrib], right, contrapose! ht2,
    rcases ht2 with ⟨M, hM⟩,
    refine ⟨M/hs0.some, λ x hx, _⟩,
    specialize hM ⟨hs0.some, x, hs0.some_spec.1, hx, rfl⟩,
    rwa [le_div_iff, mul_comm], apply lt_of_le_of_ne, exact hs _ hs0.some_spec.1,
    exact hs0.some_spec.2.symm,
    rw [not_and_distrib], right, assumption, },
  rw not_not at hs2 ht2,
  have hst2 : bdd_above (s * t) := ⟨hs2.some * ht2.some, begin
    rintros _ ⟨x, y, hx, hy, rfl⟩, apply mul_le_mul,
    exact hs2.some_spec hx, exact ht2.some_spec hy, exact ht _ hy,
    refine (hs _ hs1.some_spec).trans (hs2.some_spec hs1.some_spec),
  end⟩,

  apply le_antisymm,
  { obtain ⟨a, ha1, ha2, ha3⟩ := exists_seq_tendsto_Sup hs1 hs2,
    obtain ⟨b, hb1, hb2, hb3⟩ := exists_seq_tendsto_Sup ht1 ht2,
    let c : ℕ → ℝ := λ n, a n * b n,
    have hc1 : monotone c := monotone.mul ha1 hb1 (λ x, hs _ (ha3 _)) (λ x, ht _ (hb3 _)),
    have hc2 : filter.tendsto c filter.at_top (nhds (Sup s * Sup t)) := filter.tendsto.mul ha2 hb2,
    have hc3 : ∀ n, c n ∈ s * t := λ n, ⟨a n, b n, ha3 _, hb3 _, rfl⟩,
    refine le_of_tendsto' hc2 (λ n, (real.is_lub_Sup _ hst1 hst2).1 ⟨_, _, ha3 _, hb3 _, rfl⟩), },
  { refine cSup_le hst1 _,
    rintros _ ⟨a, b, ha, hb, rfl⟩,
    have ha1 := (real.is_lub_Sup s hs1 hs2).1 ha,
    have hb1 := (real.is_lub_Sup t ht1 ht2).1 hb,
    refine mul_le_mul ha1 hb1 (ht _ hb) le1, },
end

@[simp] lemma prod_lovasz_number_at [finite V] [finite W] (e : E) (f : F) :
  (ρ.prod ρ').lovasz_number_at (e ⊗ₜ f) = (ρ.lovasz_number_at e) * (ρ'.lovasz_number_at f) :=
begin
  rw [lovasz_number_at],
  simp_rw [prod_to_fun, inner_product_space.inner_tprod,
    norm_eq_sqrt_real_inner, inner_product_space.inner_tprod],
  rw [lovasz_number_at_eq_csupr, lovasz_number_at_eq_csupr],
  change Sup _ = Sup _ * Sup _,
  rw real.Sup_mul_Sup, congr' 1, ext1 x, split,
  { rintros ⟨⟨v, w⟩, rfl⟩, dsimp only,
    simp_rw [←real_inner_self_eq_norm_sq],
    refine ⟨inner e e / (inner (ρ v) e)^2, inner f f / (inner (ρ' w) f)^2, ⟨_, rfl⟩, ⟨_, rfl⟩, _⟩,
    conv_rhs { rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] },
    rw [real.sqrt_mul, real.sqrt_sq, real.sqrt_sq, mul_pow, ←real_inner_self_eq_norm_sq,
      ←real_inner_self_eq_norm_sq, mul_pow, mul_div, mul_div_assoc, div_mul, mul_div_assoc],
    field_simp, exact norm_nonneg f, exact norm_nonneg e, exact sq_nonneg _,},
  { rintros ⟨_, _, ⟨v, rfl⟩, ⟨w, rfl⟩, rfl⟩,
    dsimp only, rw [←real_inner_self_eq_norm_sq, ←real_inner_self_eq_norm_sq],
    rw set.mem_range, refine ⟨⟨v, w⟩, _⟩,
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real.sqrt_mul, mul_pow,
      real.sqrt_sq, real.sqrt_sq, pow_two, pow_two, pow_two, pow_two, pow_two], dsimp only,
      field_simp, congr' 1, ring1, exact norm_nonneg f, exact norm_nonneg e,
      rw pow_two, exact mul_self_nonneg _ },
  { rintros _ ⟨x, rfl⟩, dsimp only,
    apply div_nonneg; rw pow_two; exact mul_self_nonneg _,  },
  { rintros _ ⟨x, rfl⟩, dsimp only,
    apply div_nonneg; rw pow_two; exact mul_self_nonneg _,  },
end

/-- If `ρ` is an orthogonal representation of a graph `G` in `E`, then
`(x₁, x₂, …, xₖ) ↦ (ρ x₁) ⊗ (ρ x₂) ⊗ ⋯ ⊗ (ρ xₖ)` defines an orthogonal representation of the strong
product `G ⊠ G ⊠ ⋯ ⊠ G` in `E ⊗ E ⊗ ⋯ ⊗ E`. -/
@[simps] def pow (k : ℕ) : orthogonal_representation (⊠^k G) (⨂[ℝ]^k E) :=
{ to_fun := λ x, tensor_power.tpow ℝ (ρ ∘ x),
  norm_eq_one' := λ v, begin
    rw [norm_eq_sqrt_real_inner, real.sqrt_eq_iff_mul_self_eq, one_mul,
      inner_product_space.tensor_power.inner_tpow],
    simp_rw [ρ.inner_self_eq_one, finset.prod_const_one],
    exact real_inner_self_nonneg, norm_num
  end,
  inner_eq_zero_of_ne_of_not_adj' := λ v w neq nadj, begin
    rw [simple_graph.strong_pi_adj, not_and_distrib, not_forall] at nadj,
    simp_rw [not_or_distrib] at nadj,
    rw [inner_product_space.tensor_power.inner_tpow],
    rcases nadj with h|⟨x, ⟨h1, h2⟩⟩,
    { exact false.elim (h neq) },
    { rw [finset.prod_eq_zero_iff],
      exact ⟨x, finset.mem_univ _, ρ.inner_eq_zero_of_ne_of_not_adj h1 h2⟩, },
  end, }

@[simp] def vec_equiv_prod {k : ℕ} : (fin k.succ → V) ≃ (fin k → V) × V :=
{ to_fun := λ v, (λ x, v (fin.succ x), v 0),
  inv_fun := λ p x, if h : (x : ℕ) ≠ 0
    then p.1 ⟨nat.pred x, lt_of_lt_of_le (nat.pred_lt h) (nat.lt_succ_iff.mp x.2)⟩
    else p.2,
  left_inv := λ f, funext $ λ x, begin
    dsimp only, split_ifs,
    { congr' 1, ext1,
      rw [fin.succ_mk, fin.coe_mk, ←nat.succ_eq_add_one, nat.succ_pred_eq_of_pos],
      rwa pos_iff_ne_zero, },
    { push_neg at h, congr' 1, ext1, exact h.symm, },
  end,
  right_inv := λ ⟨f, v⟩, begin
    ext1, dsimp only,
    { ext1 x, split_ifs, simp_rw [fin.coe_succ, nat.pred_succ], congr' 1, ext1, refl,
      exfalso, push_neg at h, refine nat.succ_ne_zero x _, convert h,
      rw fin.coe_succ, },
    { dsimp only, rw dif_neg, push_neg, refl, },
  end }

@[simps] def vec_fun_equiv {k : ℕ} : ((fin k.succ → V) → ℝ) ≃ (((fin k → V) × V) → ℝ) :=
{ to_fun := λ f x, f (vec_equiv_prod.symm x),
  inv_fun := λ f x, f (vec_equiv_prod x),
  left_inv := λ f, funext $ λ x, begin
    dsimp only, congr' 1, simp only [equiv.symm_apply_apply],
  end,
  right_inv := λ f, funext $ λ x, begin
    dsimp only, congr' 1, simp only [equiv.apply_symm_apply],
  end }

lemma succ_vec_fun_range {k : ℕ} (f : (fin k.succ → V) → ℝ) :
  set.range f = set.range (vec_fun_equiv f) :=
begin
  ext1 x, split,
  { rintros ⟨v, rfl⟩,
    refine ⟨vec_equiv_prod v, _⟩,
    simp only [vec_equiv_prod, ne.def, dite_not, equiv.coe_fn_mk, vec_fun_equiv_apply,
      equiv.coe_fn_symm_mk, fin.succ_mk],
    congr' 1, ext, split_ifs,
    { congr' 1, ext1, rw h, refl, },
    { congr' 1, ext1, rw [fin.coe_mk, ←nat.succ_eq_add_one, nat.succ_pred_eq_of_pos],
      rw pos_iff_ne_zero, exact h, } },
  { rintros ⟨⟨g, v⟩, rfl⟩,
    simp only [vec_fun_equiv_apply, mem_range_self], },
end

@[simp] lemma pow_lovasz_number_at {k : ℕ} [finite V] (e : fin k → E) :
  (ρ.pow k).lovasz_number_at (tensor_power.tpow ℝ e) = ∏ i, ρ.lovasz_number_at (e i) :=
begin
  rw [lovasz_number_at, supr],
  induction k with k ih,
  { rw [fin.prod_univ_zero],
    have : range (λ (v : fin 0 → V), ∥tensor_power.tpow ℝ e∥ ^ 2 / inner ((ρ.pow 0) v) (tensor_power.tpow ℝ e) ^ 2) = {1},
    { ext, split,
      { rintros ⟨y, rfl⟩, dsimp only,
        rw [pow_to_fun, set.mem_singleton_iff, ←real_inner_self_eq_norm_sq,
          inner_product_space.tensor_power.inner_tpow, fin.prod_univ_zero,
          inner_product_space.tensor_power.inner_tpow, fin.prod_univ_zero, one_pow, div_one] },
      { rintros h, rw set.mem_singleton_iff at h, rw h,
        refine ⟨fin_zero_elim, _⟩, dsimp only,
        rw [←real_inner_self_eq_norm_sq, inner_product_space.tensor_power.inner_tpow,
          fin.prod_univ_zero, pow_to_fun, inner_product_space.tensor_power.inner_tpow,
          fin.prod_univ_zero, one_pow, div_one] }, },
        rw [this, cSup_singleton], },
  { rw [fin.prod_univ_succ, ←ih, succ_vec_fun_range],
    rw [lovasz_number_at, supr, real.Sup_mul_Sup],
    congr' 1,
    { ext1, split,
      { rintros ⟨y, rfl⟩,
        simp only [ne.def, vec_equiv_prod, pow_to_fun, inner_product_space.tensor_power.inner_tpow,
          comp_app, vec_fun_equiv_apply, dite_not, equiv.coe_fn_symm_mk],
        rw [fin.prod_univ_succ, ←real_inner_self_eq_norm_sq, ←real_inner_self_eq_norm_sq,
          inner_product_space.tensor_power.inner_tpow, dif_pos, fin.prod_univ_succ, mul_pow],
        rw show ∀ (a b c d : ℝ), (a * b) / (c * d) = (a / c) * (b / d),
        { intros, ring_nf, rw mul_inv, },
        refine ⟨_, _, ⟨y.2, rfl⟩, ⟨y.1, _⟩, rfl⟩,
        { dsimp only, rw [←real_inner_self_eq_norm_sq, inner_product_space.tensor_power.inner_tpow],
          congr' 2, refine finset.prod_congr rfl _,
          intros x _, rw [dif_neg],
          simp_rw [fin.coe_succ, nat.pred_succ], congr, ext1, refl,
          rw [fin.coe_succ],
          exact nat.succ_ne_zero _, },
        refl },
      { rintros ⟨_, _, ⟨x, rfl⟩, ⟨y, rfl⟩, rfl⟩,
        dsimp only, refine ⟨⟨y, x⟩, _⟩,
        simp only [ne.def, vec_equiv_prod, pow_to_fun, inner_product_space.tensor_power.inner_tpow,
          comp_app, vec_fun_equiv_apply, dite_not, equiv.coe_fn_symm_mk],
        rw [←real_inner_self_eq_norm_sq, ←real_inner_self_eq_norm_sq, ←real_inner_self_eq_norm_sq,
          inner_product_space.tensor_power.inner_tpow, inner_product_space.tensor_power.inner_tpow,
          fin.prod_univ_succ, fin.prod_univ_succ, dif_pos, mul_pow],
        rw show ∀ (a b c d : ℝ), (a * b) / (c * d) = (a / c) * (b / d),
        { intros, ring_nf, rw mul_inv, },
        congr' 3, refine finset.prod_congr rfl _,
        intros x _, rw [dif_neg], simp_rw [fin.coe_succ, ←nat.succ_eq_add_one, nat.pred_succ],
        congr, ext1, refl,
        rw [fin.coe_succ], exact nat.succ_ne_zero _,
        refl, } },
      { rintros _ ⟨v, rfl⟩, dsimp only, rw [←div_pow, pow_two], exact mul_self_nonneg _ },
      { rintros _ ⟨f, rfl⟩, dsimp only, rw [←div_pow, pow_two], exact mul_self_nonneg _ } },
end

lemma pow_lovasz_number_at' {k : ℕ} [finite V] (e : E) :
  (ρ.pow k).lovasz_number_at (tensor_power.tpow ℝ (λ i, e)) = (ρ.lovasz_number_at e)^k :=
by rw [pow_lovasz_number_at, finset.prod_const, finset.card_univ, fintype.card_fin]

end orthogonal_representation

end simple_graph
