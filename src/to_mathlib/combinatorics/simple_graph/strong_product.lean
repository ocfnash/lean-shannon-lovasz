import combinatorics.simple_graph.basic

noncomputable theory

open set function

namespace simple_graph

/-- The strong product of two graphs.

We probably won't need this for this project but it is still worth adding to Mathlib and might make
good practice for `strong_pi` below, which we do need. -/
def strong_prod {V₁ V₂ : Type*} (G₁ : simple_graph V₁) (G₂ : simple_graph V₂) :
  simple_graph (V₁ × V₂) :=
{ adj := λ x y, x ≠ y ∧ (x.1 = y.1 ∨ G₁.adj x.1 y.1) ∧ (x.2 = y.2 ∨ G₂.adj x.2 y.2),
  symm :=
  begin
    sorry,
  end,

  loopless :=
  begin
    unfold irreflexive,
    intros x,
    dunfold not,
    rintros ⟨contra1, contra2⟩,
    dunfold ne at contra1,
    dunfold not at contra1,
    apply contra1,
    refl,
  end, }

infix `⊠`:70 := strong_prod

/-- The strong product of a family of graphs: Gᵢ for `i` in some index set `ι`. -/
def strong_pi {ι : Type*} {V : ι → Type*} (G : Π i, simple_graph (V i)) : simple_graph (Π i, V i) :=
{ adj := λ x y, x ≠ y ∧ ∀ i, (x i = y i ∨ (G i).adj (x i) (y i)),
  symm := sorry,
  loopless := sorry, }

/-- The strong product of a graph with itself `k` times. -/
def strong_pow {V : Type*} (k : ℕ) (G : simple_graph V) : simple_graph (fin k → V) :=
strong_pi $ λ i, G

notation `⊠^`:70 := strong_pow

end simple_graph
