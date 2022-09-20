import linear_algebra.tensor_power

noncomputable theory

open set function
open_locale tensor_product

namespace tensor_power

variables (R : Type*) {M : Type*} [comm_semiring R] [add_comm_monoid M] [module R M]

/-- Given `v₁, v₂, …, vₙ `, their `tpow` is: `v₁ ⊗ₜ v₂ ⊗ₜ ⋯ ⊗ₜ vₙ`. -/
def tpow {n : ℕ} (v : fin n → M) : ⨂[R]^n M :=
pi_tensor_product.tprod R v

end tensor_power
