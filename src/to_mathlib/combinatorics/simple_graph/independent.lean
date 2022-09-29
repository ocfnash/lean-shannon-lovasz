import combinatorics.simple_graph.basic
import order.antichain
import set_theory.cardinal.finite

noncomputable theory

open set function

namespace simple_graph

variables {V : Type*} (G : simple_graph V)

/-- A family of vertices is independent if none of them are adjacent. -/
def independent {ι : Type*} (f : ι → V) :=
∀ i j, ¬ G.adj (f i) (f j)

/-- A subset of vertices is independent if none of them are adjacent. -/
def independent_set (s : set V) :=
G.independent (coe : s → V)

lemma independent_set_iff_is_antichain (s : set V) :
  G.independent_set s ↔ is_antichain G.adj s :=
  begin
    unfold independent_set,
    unfold independent,
    unfold is_antichain,
    unfold compl,
    split,
    {
    intro h,
    intros v hvs w hws hvw,
    lift v to s using hvs,
    lift w to s using hws,
    apply h v w
    },
    {
    intro h,
    intros i j,
    cases i with i hi,
    cases j with j hj,
    specialize h hi hj,
    by_cases hij : i = j,
    {subst hij,
    apply G.loopless i},
    {exact h hij},
    }
  end

/-- The _independence number_ of a graph is the cardinality of an independent set containing as many
vertices as possible.

Almost all useful lemmas about this definition will require the assumption that the graph is finite
since it can produce the "junk value" `0` for infinite graphs (via `nat.card`). -/
def independence_number : ℕ :=
Sup $ nat.card ∘ coe_sort '' G.independent_set

lemma independence_number_eq_bcsupr :
  G.independence_number = ⨆ s (hs : G.independent_set s), nat.card s :=
sorry

end simple_graph
