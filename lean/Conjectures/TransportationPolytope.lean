import Conjectures.TransportationTables
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Tactic

/-! The full-support real transportation polytope and its actual scalar
dilates. The strictly positive product table also proves that no cell is forced
to vanish. -/

namespace TransportationEhrhart

open scoped Pointwise

abbrev RealTable (m : ℕ) := Fin 3 → Col m → ℝ

def fits (m k : ℕ) (a : RealTable m) : Prop :=
  (∀ i j,0≤a i j) ∧ (∀ i,∑ j,a i j=(rowMargin m k i : ℝ)) ∧
    ∀ j,∑ i,a i j=(capacity k j : ℝ)

def polytope (m : ℕ) : Set (RealTable m) := {a | fits m 1 a}

theorem rowMargin_scale (m k : ℕ) (i : Fin 3) : rowMargin m k i = k*rowMargin m 1 i := by
  fin_cases i <;> simp [rowMargin,mul_comm]

theorem capacity_scale {m : ℕ} (k : ℕ) (j : Col m) : capacity k j=k*capacity 1 j := by
  cases j <;> simp [capacity,mul_comm]

theorem sum_rowMargin_one (m : ℕ) : ∑ i,rowMargin m 1 i=m+2 := by
  rw [Fin.sum_univ_three]
  simp [rowMargin]
  omega

noncomputable def positiveTable (m : ℕ) : RealTable m := fun i j =>
  (rowMargin m 1 i : ℝ)*(capacity 1 j : ℝ)/((m : ℝ)+2)

theorem positiveTable_mem (m : ℕ) : positiveTable m∈polytope m := by
  change fits m 1 _
  have den : (m : ℝ)+2≠0 := by positivity
  have sumcap : (∑ j : Col m,(capacity 1 j : ℝ))=(m : ℝ)+2 := by
    exact_mod_cast (show ∑ j : Col m,capacity 1 j=m+2 by simpa using total_capacity m 1)
  have sumrows : (∑ i,(rowMargin m 1 i : ℝ))=(m : ℝ)+2 := by exact_mod_cast sum_rowMargin_one m
  refine ⟨fun i j => by unfold positiveTable; positivity,?_,?_⟩
  · intro i
    simp only [positiveTable,←Finset.sum_div,←Finset.mul_sum,sumcap,mul_div_cancel_right₀ _ den]
  · intro j
    simp only [positiveTable,←Finset.sum_div,←Finset.sum_mul,sumrows]
    field_simp

theorem every_cell_positive {m : ℕ} (hm : 0<m) :
    ∃ a∈polytope m,∀ i j,0<a i j := by
  refine ⟨positiveTable m,positiveTable_mem m,?_⟩
  intro i j
  have row : 0<rowMargin m 1 i := by fin_cases i <;> simp [rowMargin,hm]
  have col : 0<capacity 1 j := by cases j <;> simp [capacity]
  unfold positiveTable
  positivity

theorem fits_smul {m : ℕ} (k : ℕ) {a : RealTable m} (ha : a∈polytope m) :
    fits m k ((k : ℝ) • a) := by
  obtain ⟨pos,row,col⟩ := ha
  refine ⟨fun i j => mul_nonneg (Nat.cast_nonneg _) (pos i j),?_,?_⟩
  · intro i
    change (∑ j,(k : ℝ)*a i j)=_
    rw [←Finset.mul_sum,row i,rowMargin_scale m k i,Nat.cast_mul]
  · intro j
    change (∑ i,(k : ℝ)*a i j)=_
    rw [←Finset.mul_sum,col j,capacity_scale k j,Nat.cast_mul]

theorem mem_dilate {m k : ℕ} {a : RealTable m} : a∈(k : ℝ) • polytope m ↔ fits m k a := by
  constructor
  · rintro ⟨b,h,rfl⟩
    exact fits_smul k h
  · rintro h
    by_cases zero : k=0
    · subst k
      have eq : a=0 := by
        funext i j
        have v := Finset.single_le_sum (f := a i) (fun t _ => h.1 i t) (Finset.mem_univ j)
        rw [h.2.1 i,rowMargin_scale,zero_mul,Nat.cast_zero] at v
        exact le_antisymm v (h.1 i j)
      exact ⟨positiveTable m,positiveTable_mem m,by simp [eq]⟩
    · have hk : (k : ℝ)≠0 := by exact_mod_cast zero
      refine ⟨fun i j => a i j/(k : ℝ),?_,?_⟩
      · refine ⟨fun i j => div_nonneg (h.1 i j) (Nat.cast_nonneg _),?_,?_⟩
        · intro i
          rw [←Finset.sum_div,h.2.1 i,rowMargin_scale,Nat.cast_mul]
          field_simp
        · intro j
          rw [←Finset.sum_div,h.2.2 j,capacity_scale,Nat.cast_mul]
          field_simp
      · funext i j
        change (k : ℝ)*(a i j/(k : ℝ))=a i j
        field_simp

end TransportationEhrhart
