import analysis.inner_product_space.basic

open_locale big_operators

variables {k : Type*} (E : Type*) [field k] [add_comm_group E] [module k E]

example (e : E) : ∃ (E' : subspace k E) [finite_dimensional k E'], e ∈ E' :=
begin
  have := (basis.of_vector_space k E).total_repr e,
  -- have := (basis.of_vector_space k E) '' ((basis.of_vector_space k E).repr e).support,
  refine ⟨submodule.span k ((basis.of_vector_space k E) ''
    ((basis.of_vector_space k E).repr e).support), _, _⟩,
  {  },
  -- rw [←(basis.of_vector_space k E).total_repr e],
  -- squeeze_simp,
end
