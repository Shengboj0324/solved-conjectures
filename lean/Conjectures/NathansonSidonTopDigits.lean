import Conjectures.NathansonSidonSplitDigits
import Mathlib.Algebra.BigOperators.Fin

/-! Two chosen coordinates carry complementary upper digits. The remaining
coordinates have a single possible upper digit. -/

namespace NathansonSidon

def topCount {h : ℕ} (s : DigitSplit) (a b i : Fin h) : ℕ :=
  (if i=a then s.leftCount else 1)*(if i=b then s.rightCount else 1)

def topDigit {h : ℕ} (s : DigitSplit) (a b i : Fin h) (d : Fin (topCount s a b i)) : ℕ :=
  (if i=a then s.left d.val else 0)+(if i=b then s.right d.val else 0)

theorem topCount_product {h : ℕ} (s : DigitSplit) (a b : Fin h) :
    (∏ i,topCount s a b i)=s.leftCount*s.rightCount := by
  simp only [topCount,Finset.prod_mul_distrib]
  simp

theorem topDigit_sum {h : ℕ} (s : DigitSplit) (a b : Fin h) (d : ∀ i,Fin (topCount s a b i)) :
    (∑ i,topDigit s a b i (d i))=s.left (d a).val+s.right (d b).val := by
  simp [topDigit,Finset.sum_add_distrib]

theorem topDigit_unique {h : ℕ} (s : DigitSplit) (a b : Fin h) (ab : a≠b) :
    Function.Injective (fun d : ∀ i,Fin (topCount s a b i) => ∑ i,topDigit s a b i (d i)) := by
  intro x y eq
  change (∑ i,topDigit s a b i (x i))=∑ i,topDigit s a b i (y i) at eq
  rw [topDigit_sum,topDigit_sum] at eq
  have left (d : ∀ i,Fin (topCount s a b i)) : (d a).val<s.leftCount := by
    simpa [topCount,ab] using (d a).isLt
  have right (d : ∀ i,Fin (topCount s a b i)) : (d b).val<s.rightCount := by
    simpa [topCount,ab.symm] using (d b).isLt
  obtain ⟨p,q⟩ := s.unique _ (left x) _ (right x) _ (left y) _ (right y) eq
  funext i
  apply Fin.ext
  by_cases ia : i=a
  · subst i; exact p
  by_cases ib : i=b
  · subst i; exact q
  have hx := (x i).isLt
  have hy := (y i).isLt
  simp [topCount,ia,ib] at hx hy
  omega

theorem topDigit_bounds {h : ℕ} (s : DigitSplit) (a b : Fin h) (ab : a≠b)
    (i : Fin h) (d : Fin (topCount s a b i)) :
    topDigit s a b i d≤(if i=a then s.leftMax else if i=b then s.rightMax else 0) := by
  by_cases ia : i=a
  · subst i
    simpa [topDigit,ab] using s.left_le d.val (by simpa [topCount,ab] using d.isLt)
  by_cases ib : i=b
  · subst i
    simpa [topDigit,ia] using s.right_le d.val (by simpa [topCount,ia] using d.isLt)
  simp [topDigit,ia,ib]

end NathansonSidon
