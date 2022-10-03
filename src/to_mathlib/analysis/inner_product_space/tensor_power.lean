import to_mathlib.analysis.inner_product_space.tensor_product
import to_mathlib.linear_algebra.tensor_power

noncomputable theory

open set function tensor_power
open_locale tensor_product

namespace inner_product_space

namespace tensor_power

variables (E : Type*) [inner_product_space ℝ E]

def core_zeroth_power : inner_product_space.core ℝ (⨂[ℝ]^0 E) :=
{ inner := λ x y, (pi_tensor_product.is_empty_equiv (fin 0) x) *
    (pi_tensor_product.is_empty_equiv (fin 0) y),
  conj_sym := _,
  nonneg_re := _,
  definite := _,
  add_left := _,
  smul_left := _ }

def core (k : ℕ) : inner_product_space.core ℝ (⨂[ℝ]^k E) :=
nat.rec
  (_) _ k

end tensor_power

end inner_product_space
