import combinatorics.simple_graph.basic
import set_theory.cardinal.finite
import analysis.special_functions.pow

noncomputable theory

open set function real

namespace simple_graph

variables {V : Type*} [finite V] (G : simple_graph V)

def is_independent_language {k : ℕ} (l : set (fin k → V)) : Prop :=
∀ i (w₁ w₂ : fin k → V) (hw₁ : w₁ ∈ l) (hw₂ : w₂ ∈ l), w₁ i ≠ w₂ i ∧ ¬ G.adj (w₁ i) (w₂ i)

def card_max_independent_language (k : ℕ) : ℕ :=
Sup $ nat.card ∘ coe_sort '' {l : set (fin k → V) | is_independent_language G l}

def shannon_capacity : ℝ :=
Sup $ range $ λ k, (card_max_independent_language G k : ℝ)^((1 : ℝ) / k)

end simple_graph