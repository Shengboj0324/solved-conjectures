import Conjectures.MallikDegreeGraphs
import Mathlib.Data.Finset.Sum

/-! Two complete off-diagonal blocks and two partial diagonal matchings.
The number of neighbors is computed for every subset of a part. -/

namespace MallikDegree

variable {H L : Type*} [DecidableEq H]

def family (D : Finset H) : H ⊕ L → H ⊕ L → Prop
  | .inl h,.inl j => h=j ∧ h∈D
  | .inr a,.inr b => a=b
  | _,_ => True

omit [DecidableEq H] in
theorem family_symm (D : Finset H) (x y : H ⊕ L) : family D x y ↔ family D y x := by
  cases x <;> cases y <;> simp [family,eq_comm]
  grind

omit [DecidableEq H] in
theorem exists_mem_sum (X : Finset (H ⊕ L)) (p : H ⊕ L → Prop) :
    (∃ a∈X,p a) ↔ (∃ h∈X.toLeft,p (.inl h)) ∨ (∃ l∈X.toRight,p (.inr l)) := by
  constructor
  · rintro ⟨h|l,mem,ok⟩
    · exact Or.inl ⟨h,Finset.mem_toLeft.mpr mem,ok⟩
    · exact Or.inr ⟨l,Finset.mem_toRight.mpr mem,ok⟩
  · rintro (⟨h,mem,ok⟩|⟨l,mem,ok⟩)
    · exact ⟨.inl h,Finset.mem_toLeft.mp mem,ok⟩
    · exact ⟨.inr l,Finset.mem_toRight.mp mem,ok⟩

variable [Fintype H] [Fintype L]

theorem family_neighbors (D : Finset H) (X : Finset (H ⊕ L)) :
    neighbors (family D) X=
      (if X.toRight.Nonempty then Finset.univ else X.toLeft∩D).disjSum
      (if X.toLeft.Nonempty then Finset.univ else X.toRight) := by
  classical
  ext y
  rw [mem_neighbors,exists_mem_sum]
  cases y with
  | inl h =>
    rw [Finset.inl_mem_disjSum]
    by_cases nonempty : X.toRight.Nonempty
    · obtain ⟨l,mem⟩ := nonempty
      simp only [show X.toRight.Nonempty from ⟨l,mem⟩,ite_true,Finset.mem_univ,iff_true]
      exact Or.inr ⟨l,mem,trivial⟩
    · have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
      simp [empty,family]
  | inr l =>
    rw [Finset.inr_mem_disjSum]
    by_cases nonempty : X.toLeft.Nonempty
    · obtain ⟨h,mem⟩ := nonempty
      simp only [show X.toLeft.Nonempty from ⟨h,mem⟩,ite_true,Finset.mem_univ,iff_true]
      exact Or.inl ⟨h,mem,trivial⟩
    · have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
      simp [empty,family]

omit [Fintype L] in
theorem high_subset_count (D A : Finset H) :
    A.card≤(A∩D).card+(Fintype.card H-D.card) := by
  classical
  have sub : A \ D⊆Finset.univ \ D := Finset.sdiff_subset_sdiff_left D (Finset.subset_univ _)
  have bound := Finset.card_le_card sub
  have total := Finset.card_sdiff_add_card_inter A D
  have whole := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at whole
  omega

theorem family_expands (D : Finset H) (balance : D.card+Fintype.card L=2*Fintype.card H)
    (X : Finset (H ⊕ L)) (hx : X.Nonempty) (size : X.card+Fintype.card H≤Fintype.card (H ⊕ L)) :
    X.card+Fintype.card H≤(neighbors (family D) X).card := by
  rw [family_neighbors,Finset.card_disjSum]
  have parts := X.card_toLeft_add_card_toRight
  have occupied := Finset.card_pos.mpr hx
  simp only [Fintype.card_sum] at size
  by_cases left : X.toLeft.Nonempty <;> by_cases right : X.toRight.Nonempty
  · simpa [left,right] using size
  · have empty := Finset.not_nonempty_iff_eq_empty.mp right
    simp only [left,right,ite_false,ite_true,Finset.card_univ]
    have limit := high_subset_count D X.toLeft
    have bd : D.card≤Fintype.card H := Finset.card_le_univ _
    rw [empty,Finset.card_empty,add_zero] at parts
    omega
  · have empty := Finset.not_nonempty_iff_eq_empty.mp left
    simp only [left,right,ite_true,ite_false,Finset.card_univ]
    rw [empty,Finset.card_empty,zero_add] at parts
    omega
  · have l := Finset.not_nonempty_iff_eq_empty.mp left
    have r := Finset.not_nonempty_iff_eq_empty.mp right
    simp [l,r] at parts
    omega

end MallikDegree
