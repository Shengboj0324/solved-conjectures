import Conjectures.MallikDegreePerfect
import Conjectures.MallikDegreeSimpleGraph

/-! The source definitions using unordered edges and Mathlib matching
subgraphs, including deletion of each individual edge. -/

namespace MallikDegree

def GraphExtendable {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.Connected ∧ 2*k+2≤Fintype.card V ∧
    (∃ M : G.Subgraph,M.IsMatching ∧ M.edgeSet.ncard=k) ∧
    ∀ M : G.Subgraph,M.IsMatching → M.edgeSet.ncard=k → ∃ P : G.Subgraph,P.IsPerfectMatching ∧ M≤P

def GraphMinimal {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  GraphExtendable G k ∧ ∀ e∈G.edgeSet,¬GraphExtendable (G.deleteEdges {e}) k

variable {α : Type*} [Fintype α] {R : α → α → Prop} {k : ℕ}

theorem graph_extendable_iff : GraphExtendable (graph R) k ↔ Extendable R k := by
  classical
  constructor
  · rintro ⟨connected,order,⟨M,mat,count⟩,extend⟩
    have card := (edgePairs_card M).trans count
    obtain ⟨u,v,_,edge⟩ := tupleEdges_surjective _ card (edgePairs_matching mat)
    refine ⟨connected,by simpa [two_mul] using order,⟨u,v,edge⟩,extends_iff_every_matching.mpr ?_⟩
    intro E size matching
    let B := subOfEdges E matching.1
    have bm : B.IsMatching := subOfEdges_matching E matching
    have countB : B.edgeSet.ncard=k := by rw [←edgePairs_card,pairs_of_edges,size]
    obtain ⟨P,perf,sub⟩ := extend B bm countB
    obtain ⟨f,edges,pairs⟩ := permutation_of_perfect perf
    exact ⟨f,edges,fun e he => (pairs _ _).mp (sub.2 (show B.Adj (.inl e.1) (.inr e.2) from he))⟩
  · rintro ⟨connected,order,⟨u,v,edges⟩,extend⟩
    let E := tupleEdges u v
    have em : EdgeMatching R E := tupleEdges_matching u v edges
    let B := subOfEdges E em.1
    have count : B.edgeSet.ncard=k := by rw [←edgePairs_card,pairs_of_edges,tupleEdges_card]
    refine ⟨connected,by simpa [two_mul] using order,⟨B,subOfEdges_matching E em,count⟩,?_⟩
    intro M mat size
    obtain ⟨f,edge,pairs⟩ := (extends_iff_every_matching.mp extend) _ ((edgePairs_card M).trans size) (edgePairs_matching mat)
    have perf := perfectSubgraph_perfect f edge
    exact ⟨perfectSubgraph f edge,perf,le_spanning_of_pairs perf.2 fun x y adj =>
      pairs (x,y) ((mem_edgePairs M x y).mpr adj)⟩

theorem graph_minimal_of_minimal (minimal : Minimal R k) : GraphMinimal (graph R) k := by
  refine ⟨graph_extendable_iff.mpr minimal.1,?_⟩
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    have edge := (graph R).mem_edgeSet.mp he
    cases a with
    | inl x => cases b with
      | inl z => exact False.elim edge
      | inr y =>
        rw [←graph_deleted,graph_extendable_iff]
        exact minimal.2 x y edge
    | inr y => cases b with
      | inr z => exact False.elim edge
      | inl x =>
        rw [Sym2.eq_swap (a := Sum.inr y) (b := Sum.inl x),←graph_deleted,graph_extendable_iff]
        exact minimal.2 x y edge

end MallikDegree
