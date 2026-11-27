import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! The square of the stars-and-bars coefficient in the shifted binomial
basis. Both uses of Vandermonde are finite identities in the natural numbers. -/

namespace TransportationEhrhart

open Finset

theorem overlap_sum (h m : ℕ) : ∑ j ∈ range (m+1),m.choose j*h.choose j=(h+m).choose m := by
  rw [Nat.add_choose_eq,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply sum_congr rfl
  intro j hj
  rw [Nat.choose_symm (mem_range_succ_iff.mp hj),mul_comm]

theorem basis_split {m j : ℕ} (hj : j≤m) (k : ℕ) :
    (k+2*m-j).choose (2*m)=∑ h ∈ range (m+1),(k+m).choose (m+h)*(m-j).choose (m-h) := by
  let t (s : ℕ) := (m-j).choose s*(k+m).choose (2*m-s)
  have split : k+2*m-j=(m-j)+(k+m) := by omega
  rw [split,Nat.add_choose_eq,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ s ∈ range (2*m+1),t s)=_
  calc
    _ = ∑ s ∈ range (m+1),t s := by
      symm
      apply sum_subset (range_mono (by omega))
      intro s _ hs
      have big : m-j<s := by simp only [mem_range] at hs; omega
      simp [t,Nat.choose_eq_zero_of_lt big]
    _ = ∑ h ∈ range (m+1),t (m-h) := by simpa using (sum_range_reflect t (m+1)).symm
    _ = _ := by
      apply sum_congr rfl
      intro h hh
      have le := mem_range_succ_iff.mp hh
      have eq : 2*m-(m-h)=m+h := by omega
      unfold t
      rw [eq,mul_comm]

theorem choose_nested {m j h : ℕ} (hj : j≤m) (hh : h≤m) :
    m.choose j*(m-j).choose (m-h)=m.choose h*h.choose j := by
  by_cases le : j≤h
  · have rev := Nat.choose_symm (n := m-j) (k := h-j) (by omega)
    rw [show m-j-(h-j)=m-h by omega] at rev
    rw [rev,← Nat.choose_mul le]
  · have high : m-j<m-h := by omega
    rw [Nat.choose_eq_zero_of_lt high,Nat.choose_eq_zero_of_lt (show h<j by omega),mul_zero,mul_zero]

theorem inner_basis {m h : ℕ} (hh : h≤m) :
    ∑ j ∈ range (m+1),m.choose j^2*(m-j).choose (m-h)=m.choose h*(h+m).choose m := by
  rw [←overlap_sum,Finset.mul_sum]
  apply sum_congr rfl
  intro j hj
  have nested := choose_nested (mem_range_succ_iff.mp hj) hh
  calc
    _ = m.choose j*(m.choose j*(m-j).choose (m-h)) := by ring
    _ = _ := by rw [nested]; ring

theorem shifted_choose_product (k m h : ℕ) :
    (k+m).choose (m+h)*(h+m).choose m=(k+m).choose m*k.choose h := by
  have q := Nat.choose_mul (n := k+m) (k := m+h) (s := m) (by omega)
  simpa [Nat.add_comm h m] using q

theorem square_binomial_series (m k : ℕ) :
    ∑ j ∈ range (m+1),m.choose j^2*(k+2*m-j).choose (2*m)=(k+m).choose m^2 := by
  calc
    _ = ∑ j ∈ range (m+1),∑ h ∈ range (m+1),
        (k+m).choose (m+h)*(m.choose j^2*(m-j).choose (m-h)) := by
      apply sum_congr rfl
      intro j hj
      rw [basis_split (mem_range_succ_iff.mp hj),Finset.mul_sum]
      apply sum_congr rfl
      intro h _
      ring
    _ = ∑ h ∈ range (m+1),(k+m).choose (m+h)*(m.choose h*(h+m).choose m) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro h hh
      rw [←Finset.mul_sum,inner_basis (mem_range_succ_iff.mp hh)]
    _ = (k+m).choose m*∑ h ∈ range (m+1),m.choose h*k.choose h := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro h _
      calc
        _ = m.choose h*((k+m).choose (m+h)*(h+m).choose m) := by ring
        _ = _ := by rw [shifted_choose_product]; ring
    _ = _ := by rw [overlap_sum,sq]

end TransportationEhrhart
