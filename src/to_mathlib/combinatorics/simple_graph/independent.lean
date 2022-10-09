import combinatorics.simple_graph.basic
import order.antichain
import set_theory.cardinal.finite
import data.fintype.order

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

instance independent_set_fintype [fintype V] :
  fintype $ subtype G.independent_set :=
fintype.of_injective (coe : subtype G.independent_set → set V) subtype.coe_injective

lemma independent_number_bdd_above [fintype V] :
  bdd_above $ nat.card ∘ coe_sort '' G.independent_set :=
begin
  obtain ⟨M, hM⟩ := fintype.exists_le (nat.card ∘ coe_sort : subtype G.independent_set → ℕ),
  refine ⟨M, _⟩, rintros _ ⟨S, ⟨hx, rfl⟩⟩,
  refine (hM ⟨S, hx⟩).trans _, refl,
end

lemma nat.find_eq_find_of_iff {p q : ℕ → Prop}
  [decidable_pred (λ (n : ℕ), q n)] [decidable_pred (λ (n : ℕ), p n)]
  (P : ∃ n, p n) (Q : ∃ n, q n) (h : ∀ n, p n ↔ q n) :
  nat.find P = nat.find Q :=
begin
  have eq1 : p = q,
  { ext, apply h },
  unfreezingI { subst eq1 }, resetI,
  have eq1 : P = Q := rfl,
  rw eq1, congr,
end

lemma nat.supr_pos {p : Prop} (h : p) (f : p → ℕ) :
  (⨆ (i : p), f i) = f h :=
begin
  rw [supr, nat.Sup_def], swap,
  { refine ⟨f h, _⟩, rintros _ ⟨h', rfl⟩, exact le_refl _, },
  rw nat.find_eq_iff, split,
  { rintros _ ⟨h', rfl⟩, exact le_refl _ },
  { rintros m hm r,
    specialize r (f h) ⟨_, rfl⟩, linarith }
end

lemma independence_number_eq_bcsupr [fintype V] :
  G.independence_number = ⨆ s (hs : G.independent_set s), nat.card s :=
begin
  classical,
  obtain ⟨M, hM⟩ := G.independent_number_bdd_above,
  rw [independence_number, supr, nat.Sup_def, nat.Sup_def],
  work_on_goal 2
  { refine ⟨M, _⟩, rintros n ⟨S, rfl⟩,
    dsimp only, rw [supr, nat.Sup_def], swap,
    { refine ⟨M, _⟩, rintros n ⟨hS, rfl⟩, dsimp only,
      apply hM, rw [set.mem_image], exact ⟨_, hS, rfl⟩, } },
  work_on_goal 3
  { refine ⟨M, _⟩, rintros n ⟨S, hS, rfl⟩, apply hM,
    rw set.mem_image, exact ⟨_, hS, rfl⟩, },
  work_on_goal 2
  { generalize_proofs h,
    refine nat.find_le _, rintros _ ⟨hS, rfl⟩, dsimp only,
    apply hM, refine ⟨_, hS, rfl⟩, },
  { generalize_proofs h₁ h₂,
    refine nat.find_eq_find_of_iff _ _ (λ n, _), split,
    { rintros h _ ⟨S, rfl⟩, dsimp only,
      rw [supr, nat.Sup_def], swap,
      { refine ⟨M, _⟩, rintros _ ⟨hS, rfl⟩, dsimp only, apply hM,
        exact ⟨_, hS, rfl⟩, },
      rw nat.find_le_iff, refine ⟨n, le_refl _, _⟩,
      rintro m ⟨hS, rfl⟩, apply h, exact ⟨_, hS, rfl⟩, },
    { rintros h _ ⟨S, hS, rfl⟩, apply h, refine ⟨S, _⟩,
      dsimp only, rw [nat.supr_pos], exact hS },
  },
end

lemma exists_maximal_independent_set [fintype V] : ∃ (s : set V) (hs : G.independent_set s),
  nat.card s = G.independence_number :=
begin
  rw independence_number,
  have ne : (nat.card ∘ coe_sort '' G.independent_set).nonempty,
  { refine ⟨_, ⟨∅, λ x, false.elim (not_mem_empty x.1 x.2), rfl⟩⟩, },
  haveI : nonempty (nat.card ∘ coe_sort '' G.independent_set) :=
    ⟨⟨ne.some, ne.some_spec⟩⟩,
  have : G.independence_number ∈ _:= nat.Sup_mem _ _,
  rw [set.mem_image] at this,
  obtain ⟨s, hs1, hs2⟩ := this,
  refine ⟨s, hs1, _⟩,
  simp only [comp_app] at hs2, rw hs2, refl, assumption,
  haveI : fintype (nat.card ∘ coe_sort '' G.independent_set),
  { apply_instance, },
  obtain ⟨M, hM⟩ := @fintype.exists_le (nat.card ∘ coe_sort '' G.independent_set)
    _ _ _ (nat.card ∘ coe_sort '' G.independent_set) _ id,
  refine ⟨M, _⟩,
  rintros _ ⟨s, hs, rfl⟩,
  specialize hM ⟨nat.card s, ⟨s, hs, rfl⟩⟩,
  convert hM,
end

def maximal_independent_set [fintype V] : set V := G.exists_maximal_independent_set.some

lemma maximal_independent_set_is_independent [fintype V] :
  G.independent_set G.maximal_independent_set :=
G.exists_maximal_independent_set.some_spec.some

lemma card_maximal_independent_set [fintype V] :
  nat.card G.maximal_independent_set = G.independence_number :=
G.exists_maximal_independent_set.some_spec.some_spec

instance [fintype V] : fintype G.maximal_independent_set :=
fintype.of_finite (maximal_independent_set G)

end simple_graph
