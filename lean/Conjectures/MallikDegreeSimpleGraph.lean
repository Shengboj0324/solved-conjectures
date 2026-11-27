import Conjectures.MallikDegreeCounts
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! Identify the counted neighbors and edges with Mathlib's simple graph
and identify the removal of any bipartite edge with graph edge deletion. -/

namespace MallikDegree

variable {α : Type*}

theorem graph_bipartite (R : α → α → Prop) : (graph R).IsBipartite := by
  apply SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mpr
  refine ⟨Set.range (Sum.inl : α → α ⊕ α),Set.range Sum.inr,?_,?_⟩
  · apply Set.disjoint_left.mpr
    rintro _ ⟨a,rfl⟩ ⟨b,eq⟩
    cases eq
  · intro x y edge
    cases x with
    | inl a =>
      cases y with
      | inl b => exact False.elim edge
      | inr b => exact Or.inl ⟨⟨a,rfl⟩,b,rfl⟩
    | inr a =>
      cases y with
      | inl b => exact Or.inr ⟨⟨a,rfl⟩,b,rfl⟩
      | inr b => exact False.elim edge

theorem graph_deleted (R : α → α → Prop) (x y : α) :
    graph (deleted R x y)=(graph R).deleteEdges {s(Sum.inl x,Sum.inr y)} := by
  ext a b
  rw [SimpleGraph.deleteEdges_adj]
  cases a <;> cases b <;> simp [graph,across,deleted] <;> tauto

variable [Fintype α]

noncomputable local instance {R : α → α → Prop} : DecidableRel (graph R).Adj :=
  fun _ _ => Classical.propDecidable _

theorem graph_degree_left (R : α → α → Prop) (x : α) : (graph R).degree (.inl x)=degree R x := by
  classical
  have same : (graph R).neighborFinset (.inl x)=(neighbors R {x}).map Function.Embedding.inr := by
    ext y
    rw [SimpleGraph.mem_neighborFinset]
    cases y with
    | inl b => simp [graph,across]
    | inr b => simp [graph,across,mem_neighbors]
  rw [←SimpleGraph.card_neighborFinset_eq_degree,same,Finset.card_map]
  rfl

theorem graph_degree_right (R : α → α → Prop) (y : α) :
    (graph R).degree (.inr y)=degree (fun x z => R z x) y := by
  classical
  have same : (graph R).neighborFinset (.inr y)=(neighbors (fun x z => R z x) {y}).map Function.Embedding.inl := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    cases x with
    | inl b => simp [graph,across,mem_neighbors]
    | inr b => simp [graph,across]
  rw [←SimpleGraph.card_neighborFinset_eq_degree,same,Finset.card_map]
  rfl

theorem graph_degree_count (R : α → α → Prop) (d : ℕ) :
    (Finset.univ.filter fun x => (graph R).degree x=d).card=degreeCount R d := by
  classical
  simp only [degreeCount,Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_sum_type,
    graph_degree_left,graph_degree_right]

theorem graph_edges_symmetric (R : α → α → Prop) (sym : ∀ x y,R x y ↔ R y x) :
    (graph R).edgeFinset.card=edges R := by
  classical
  have same : (fun x y => R y x)=R := by funext x y; exact propext (sym y x)
  have count := (graph R).sum_degrees_eq_twice_card_edges
  simp only [Fintype.sum_sum_type,graph_degree_left,graph_degree_right,same] at count
  unfold edges
  omega

end MallikDegree
