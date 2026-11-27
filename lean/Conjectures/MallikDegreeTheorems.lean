import Conjectures.MallikDegreeCounterfamily
import Conjectures.MallikDegreeLiteral

/-! The counterexample to Conjecture 8.9 for every k and every stated
even order, in terms of Mathlib's literal edges, degrees and matchings. -/

namespace MallikDegree

abbrev Side (k t : ℕ) := Fin k ⊕ Fin t
abbrev Vertex (k t : ℕ) := Side k t ⊕ Side k t
def counterGraph (k t : ℕ) : SimpleGraph (Vertex k t) := graph (relation k t)

noncomputable def verticesOfDegree {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Finset V := by
  classical exact Finset.univ.filter fun v => G.degree v=d

theorem literal_counts {k t : ℕ} (lo : k+2≤t) :
    Fintype.card (Vertex k t)=2*(k+t) ∧ (counterGraph k t).edgeSet.ncard=2*k*t+t+(2*k-t) ∧
      (verticesOfDegree (counterGraph k t) (k+1)).card=2*t := by
  classical
  obtain ⟨order,ec,dc⟩ := exact_counts lo
  have es := graph_edges_symmetric (relation k t) (family_symm (marked k t))
  have ds := graph_degree_count (relation k t) (k+1)
  refine ⟨order,?_,?_⟩
  · change (graph (relation k t)).edgeSet.ncard=_
    rw [Set.ncard_eq_toFinset_card']
    exact es.trans ec
  · exact ds.trans dc

theorem minimal_counterexample {k t : ℕ} (hk : 3≤k) (lo : k+2≤t) (hi : t≤2*k-1) :
    (counterGraph k t).IsBipartite ∧ GraphMinimal (counterGraph k t) k ∧
      ((verticesOfDegree (counterGraph k t) (k+1)).card : ℝ) <
      2*(((counterGraph k t).edgeSet.ncard : ℝ)-(Fintype.card (Vertex k t) : ℝ)+2*k)/(2*k-1) := by
  refine ⟨graph_bipartite _,graph_minimal_of_minimal (family_minimal hk lo hi),?_⟩
  obtain ⟨n,m,d⟩ := literal_counts lo
  obtain ⟨_,ed,deg⟩ := exact_counts lo
  have failed := violates_degree_bound hk lo hi
  rw [ed,deg] at failed
  rw [n,m,d]
  push_cast at failed ⊢
  exact failed

theorem every_even_order {k n : ℕ} (hk : 3≤k) (even : Even n) (lo : 4*k+4≤n) (hi : n≤6*k-2) :
    ∃ t : ℕ,Fintype.card (Vertex k t)=n ∧ (counterGraph k t).IsBipartite ∧
      GraphMinimal (counterGraph k t) k ∧ ((verticesOfDegree (counterGraph k t) (k+1)).card : ℝ)<
        2*(((counterGraph k t).edgeSet.ncard : ℝ)-(n : ℝ)+2*k)/(2*k-1) := by
  obtain ⟨t,order,low,high,_,_⟩ := all_even_orders hk even lo hi
  have count := (literal_counts low).1.trans order.symm
  obtain ⟨bip,minimal,fail⟩ := minimal_counterexample hk low high
  exact ⟨t,count,bip,minimal,count ▸ fail⟩

theorem smallest_member :
    Fintype.card (Vertex 3 5)=16 ∧ (counterGraph 3 5).IsBipartite ∧ GraphMinimal (counterGraph 3 5) 3 ∧
      (counterGraph 3 5).edgeSet.ncard=36 ∧ (verticesOfDegree (counterGraph 3 5) 4).card=10 ∧
      ((verticesOfDegree (counterGraph 3 5) 4).card : ℝ)<52/5 := by
  obtain ⟨n,m,d⟩ := literal_counts (k := 3) (t := 5) (by decide)
  obtain ⟨bip,minimal,_⟩ := minimal_counterexample (k := 3) (t := 5) (by decide) (by decide) (by decide)
  exact ⟨n,bip,minimal,m,d,by rw [d]; norm_num⟩

theorem gap_at_first_order {k : ℕ} (hk : 3≤k) :
    2*((edges (relation k (k+2)) : ℝ)-2*((k : ℝ)+(k+2))+2*k)/(2*k-1)-
      (degreeCount (relation k (k+2)) (k+1) : ℝ)=2*((k : ℝ)-2)/(2*k-1) := by
  have eq := exact_gap (t := k+2) hk (le_refl _)
  have delta : 2*k-(k+2)=k-2 := by omega
  rw [delta] at eq
  push_cast [Nat.cast_sub (by omega : 2≤k)] at eq
  exact eq

theorem comparison_range {k t : ℕ} (lo : k+2≤t) (hi : t≤2*k-1) :
    2*(k+t)<6*k ∧ k+t+2≤degreeCount (relation k t) (k+1) := by
  rw [(exact_counts lo).2.2]
  omega

end MallikDegree
