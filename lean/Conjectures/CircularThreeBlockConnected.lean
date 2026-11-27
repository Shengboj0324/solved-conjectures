import Conjectures.CircularThreeBlockDegree
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The degree formula gives each pair of vertices a common neighbor. -/

namespace CircularIndex.Insertion.ThreeBlock

theorem common_neighbor {g : ℕ} (hg : 15≤g) (K : Packing g) (u v : Fin (vertexCount g)) :
    ∃ w, (schedule hg K).graph.Adj u w ∧ (schedule hg K).graph.Adj v w := by
  let G := (schedule hg K).graph
  have lower (x : Fin (vertexCount g)) : 4*g+2≤G.degree x := by
    change _≤(schedule hg K).graph.degree x
    rw [degree_formula hg K]
    split <;> omega
  have meet : ¬ Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
    intro disjoint
    have bound := Finset.card_le_univ (G.neighborFinset u ∪ G.neighborFinset v)
    rw [Finset.card_union_of_disjoint disjoint, G.card_neighborFinset_eq_degree,
      G.card_neighborFinset_eq_degree, Fintype.card_fin] at bound
    have large : vertexCount g < G.degree u + G.degree v := by
      calc
        vertexCount g < (4*g+2)+(4*g+2) := by unfold vertexCount; omega
        _ ≤ _ := Nat.add_le_add (lower u) (lower v)
    exact (Nat.not_lt_of_ge bound) large
  obtain ⟨w,hu,hv⟩ := Finset.not_disjoint_iff.mp meet
  exact ⟨w,(G.mem_neighborFinset u w).mp hu,(G.mem_neighborFinset v w).mp hv⟩

theorem graph_connected {g : ℕ} (hg : 15≤g) (K : Packing g) :
    (schedule hg K).graph.Connected := by
  have : Nonempty (Fin (vertexCount g)) := ⟨⟨0,by simp [vertexCount]⟩⟩
  refine ⟨fun u v => ?_⟩
  obtain ⟨w,hu,hv⟩ := common_neighbor hg K u v
  exact hu.reachable.trans hv.symm.reachable

end CircularIndex.Insertion.ThreeBlock
