import Conjectures.TransportationRows

/-! Integral points in the three-row transportation family. The first column
has twice the usual capacity. The two top rows uniquely determine the third. -/

namespace TransportationEhrhart

abbrev Col (m : ℕ) := Option (Fin m)
abbrev RowPair (m k : ℕ) := Row (Col m) k × Row (Col m) k

def capacity {m : ℕ} (k : ℕ) : Col m → ℕ
  | none => 2*k
  | some _ => k

def rowMargin (m k : ℕ) : Fin 3 → ℕ := ![k,k,m*k]

abbrev Table (m k : ℕ) := {a : Fin 3 → Col m → ℕ //
  (∀ i,∑ j,a i j=rowMargin m k i) ∧ ∀ j,∑ i,a i j=capacity k j}

def Admissible {m k : ℕ} (p : RowPair m k) :=
  ∀ j : Fin m,p.1.val (some j)+p.2.val (some j) ≤ k

theorem all_capacities {m k : ℕ} {p : RowPair m k} (ok : Admissible p) (j : Col m) :
    p.1.val j+p.2.val j ≤ capacity k j := by
  cases j with
  | none =>
    have a := entry_le p.1 none
    have b := entry_le p.2 none
    change _ ≤ 2*k
    omega
  | some j => exact ok j

theorem total_capacity (m k : ℕ) : ∑ j : Col m,capacity k j=(m+2)*k := by
  rw [Fintype.sum_option]
  simp [capacity,add_mul]
  omega

def topRows {m k : ℕ} (t : Table m k) : RowPair m k :=
  (⟨t.val 0,t.property.1 0⟩,⟨t.val 1,t.property.1 1⟩)

theorem top_admissible {m k : ℕ} (t : Table m k) : Admissible (topRows t) := by
  intro j
  have c := t.property.2 (some j)
  rw [Fin.sum_univ_three] at c
  change t.val 0 (some j)+t.val 1 (some j) ≤ k
  change _ = k at c
  omega

def bottom {m k : ℕ} (p : RowPair m k) (j : Col m) : ℕ :=
  capacity k j-(p.1.val j+p.2.val j)

theorem full_column {m k : ℕ} {p : RowPair m k} (ok : Admissible p) (j : Col m) :
    p.1.val j+p.2.val j+bottom p j=capacity k j := Nat.add_sub_of_le (all_capacities ok j)

theorem bottom_total {m k : ℕ} {p : RowPair m k} (ok : Admissible p) : ∑ j,bottom p j=m*k := by
  have total := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => full_column ok j)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,p.1.property,p.2.property,total_capacity] at total
  rw [add_mul,two_mul] at total
  omega

def makeTable {m k : ℕ} (p : RowPair m k) (ok : Admissible p) : Table m k :=
  ⟨![p.1.val,p.2.val,bottom p],by
    constructor
    · intro i
      fin_cases i
      · exact p.1.property
      · exact p.2.property
      · exact bottom_total ok
    · intro j
      rw [Fin.sum_univ_three]
      exact full_column ok j⟩

def tableEquiv (m k : ℕ) : Table m k ≃ {p : RowPair m k // Admissible p} where
  toFun t := ⟨topRows t,top_admissible t⟩
  invFun p := makeTable p.val p.property
  left_inv t := by
    apply Subtype.ext
    funext i j
    fin_cases i
    · rfl
    · rfl
    · change capacity k j-(t.val 0 j+t.val 1 j)=t.val 2 j
      have h := t.property.2 j
      rw [Fin.sum_univ_three] at h
      omega
  right_inv _ := rfl

end TransportationEhrhart
