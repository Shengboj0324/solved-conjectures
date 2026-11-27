import Conjectures.TransportationGrouping
import Conjectures.TransportationPolytope

/-! A unit slot for each unit of the row and column margins. -/

namespace TransportationEhrhart

open Finset Matrix

abbrev Slot (m : ℕ) := Fin 2 ⊕ Fin m

def slotRow {m : ℕ} : Slot m → Fin 3 := Sum.elim Fin.castSucc (fun _ => 2)
def slotColumn {m : ℕ} : Slot m → Col m := Sum.elim (fun _ => none) some

theorem fiber_count {ι K : Type*} [Fintype ι] [DecidableEq K] (g : ι → K) (b : K) :
    (fiber g b).card=∑ x,if g x=b then 1 else 0 := by simp [fiber]

theorem row_slots (m : ℕ) (i : Fin 3) : (fiber (@slotRow m) i).card=rowMargin m 1 i := by
  rw [fiber_count,Fintype.sum_sum_type]
  fin_cases i <;> simp [slotRow,Fin.sum_univ_two,rowMargin]

theorem column_slots (m : ℕ) (j : Col m) : (fiber slotColumn j).card=capacity 1 j := by
  rw [fiber_count,Fintype.sum_sum_type]
  cases j <;> simp [slotColumn,capacity]

theorem row_slots_pos {m : ℕ} (hm : 0<m) (i : Fin 3) : 0<(fiber (@slotRow m) i).card := by
  rw [row_slots]
  fin_cases i <;> simp [rowMargin,hm]

theorem column_slots_pos {m : ℕ} (j : Col m) : 0<(fiber slotColumn j).card := by
  rw [column_slots]
  cases j <;> simp [capacity]

theorem grouped_row {ι A B R : Type*} [Fintype ι] [DecidableEq A] [Fintype B] [DecidableEq B]
    [AddCommMonoid R] (r : ι → A) (c : ι → B) (x : Matrix ι ι R) (i : A) :
    ∑ j,grouped r c x i j=∑ t ∈ fiber r i,∑ s,x t s := by
  unfold grouped
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  exact sum_over_labels c (x t)

theorem grouped_column {ι A B R : Type*} [Fintype ι] [Fintype A] [DecidableEq A] [DecidableEq B]
    [AddCommMonoid R] (r : ι → A) (c : ι → B) (x : Matrix ι ι R) (j : B) :
    ∑ i,grouped r c x i j=∑ s ∈ fiber c j,∑ t,x t s := by
  calc
    _ = ∑ i,grouped c r x.transpose j i := by
      apply sum_congr rfl
      intro i _
      exact sum_comm
    _ = _ := grouped_row c r x.transpose j

theorem regroup_mem {m : ℕ} {x : Matrix (Slot m) (Slot m) ℝ} (hx : x ∈ doublyStochastic ℝ (Slot m)) :
    grouping slotRow slotColumn x∈polytope m := by
  obtain ⟨nn,row,col⟩ := mem_doublyStochastic_iff_sum.mp hx
  refine ⟨fun i j => sum_nonneg (s := fiber slotRow i) (fun t _ => sum_nonneg (s := fiber slotColumn j) fun s _ => nn t s),?_,?_⟩
  · intro i
    change ∑ j,grouped slotRow slotColumn x i j=_
    rw [grouped_row]
    simp [row,row_slots]
  · intro j
    change ∑ i,grouped slotRow slotColumn x i j=_
    rw [grouped_column]
    simp [col,column_slots]

theorem polytope_as_image {m : ℕ} (hm : 0<m) :
    polytope m=grouping slotRow slotColumn '' (doublyStochastic ℝ (Slot m) : Set _) := by
  ext a
  constructor
  · rintro ⟨nn,row,col⟩
    refine ⟨expandSlots slotRow slotColumn a,expanded_stochastic _ _ (row_slots_pos hm) column_slots_pos
      nn (fun i => by rw [row_slots]; exact row i) (fun j => by rw [column_slots]; exact col j),?_⟩
    exact group_expansion _ _ (row_slots_pos hm) column_slots_pos a
  · rintro ⟨x,hx,rfl⟩
    exact regroup_mem hx

end TransportationEhrhart
