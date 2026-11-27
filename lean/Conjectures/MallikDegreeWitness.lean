import Conjectures.MallikDegreeTheorems
import Conjectures.MallikDegreeRelabel

/-! Identify the eight literal deletion-search row masks with the smallest
member of the infinite family by explicit permutations of both sides. -/

namespace MallikDegree

def searchRow : Fin 8 → ℕ := ![108,228,116,155,187,102,101,155]
def searchRelation (x y : Fin 8) : Prop := (searchRow x).testBit y.val=true

def labelLeft : Side 3 5 → Fin 8 := Sum.elim ![4,3,7] ![0,1,2,5,6]
def labelRight : Side 3 5 → Fin 8 := Sum.elim ![5,6,2] ![3,7,4,1,0]

private theorem left_bijective : Function.Bijective labelLeft := by
  constructor <;> decide
private theorem right_bijective : Function.Bijective labelRight := by
  constructor <;> decide

noncomputable def leftLabels := Equiv.ofBijective labelLeft left_bijective
noncomputable def rightLabels := Equiv.ofBijective labelRight right_bijective

theorem literal_rows (x y : Side 3 5) : relation 3 5 x y ↔ searchRelation (leftLabels x) (rightLabels y) := by
  change relation 3 5 x y ↔ searchRelation (labelLeft x) (labelRight y)
  rcases x with x|x <;> rcases y with y|y <;> fin_cases x <;> fin_cases y <;> simp only [relation, family, searchRelation] <;> decide

noncomputable def searchIso : counterGraph 3 5 ≃g graph searchRelation := graphIso leftLabels rightLabels literal_rows

theorem search_minimal : GraphMinimal (graph searchRelation) 3 := graph_minimal_of_minimal
  (relabel_minimal leftLabels rightLabels literal_rows (family_minimal (by decide) (by decide) (by decide)))

theorem search_count : (graph searchRelation).edgeSet.ncard=36 ∧ (verticesOfDegree (graph searchRelation) 4).card=10 := by
  classical
  obtain ⟨_,_,_,edge,small,_⟩ := smallest_member
  have edges := searchIso.card_edgeFinset_eq
  rw [Set.ncard_eq_toFinset_card'] at edge ⊢
  have eq : (verticesOfDegree (counterGraph 3 5) 4).map searchIso.toEquiv.toEmbedding=
      verticesOfDegree (graph searchRelation) 4 := by
    ext y
    simp only [verticesOfDegree, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (searchIso.degree_eq x).trans hx
    · intro hy
      obtain ⟨x,rfl⟩ := searchIso.surjective y
      exact ⟨x,(searchIso.degree_eq x).symm.trans hy,rfl⟩
  refine ⟨edges.symm.trans edge,?_⟩
  rw [←eq,Finset.card_map,small]

end MallikDegree
