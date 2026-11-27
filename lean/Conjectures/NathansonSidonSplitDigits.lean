import Mathlib.Tactic

/-! Complementary binary digits distribute the top level of a mixed-radix
Sidon system in any prescribed dyadic proportion. -/

namespace NathansonSidon

structure DigitSplit where
  leftCount : ℕ
  rightCount : ℕ
  leftMax : ℕ
  rightMax : ℕ
  left : ℕ → ℕ
  right : ℕ → ℕ
  left_le : ∀ x<leftCount,left x≤leftMax
  right_le : ∀ x<rightCount,right x≤rightMax
  unique : ∀ x<leftCount,∀ y<rightCount,∀ x'<leftCount,∀ y'<rightCount,
    left x+right y=left x'+right y' → x=x' ∧ y=y'

def DigitSplit.empty : DigitSplit where
  leftCount := 1
  rightCount := 1
  leftMax := 0
  rightMax := 0
  left := fun _ => 0
  right := fun _ => 0
  left_le := by intros; rfl
  right_le := by intros; rfl
  unique := by intros; omega

def DigitSplit.swap (s : DigitSplit) : DigitSplit where
  leftCount := s.rightCount
  rightCount := s.leftCount
  leftMax := s.rightMax
  rightMax := s.leftMax
  left := s.right
  right := s.left
  left_le := s.right_le
  right_le := s.left_le
  unique := by
    intro x hx y hy x' hx' y' hy' eq
    obtain ⟨a,b⟩ := s.unique y hy x hx y' hy' x' hx' (by simpa only [add_comm] using eq)
    exact ⟨b,a⟩

def DigitSplit.doubleLeft (s : DigitSplit) : DigitSplit where
  leftCount := 2*s.leftCount
  rightCount := s.rightCount
  leftMax := 2*s.leftMax+1
  rightMax := 2*s.rightMax
  left := fun x => 2*s.left (x/2)+x%2
  right := fun y => 2*s.right y
  left_le := by
    intro x hx
    have := s.left_le (x/2) (by omega)
    omega
  right_le := fun y hy => Nat.mul_le_mul_left 2 (s.right_le y hy)
  unique := by
    intro x hx y hy x' hx' y' hy' eq
    have e : s.left (x/2)+s.right y=s.left (x'/2)+s.right y' := by omega
    obtain ⟨a,b⟩ := s.unique (x/2) (by omega) y hy (x'/2) (by omega) y' hy' e
    exact ⟨by omega,b⟩

theorem balanced_binary_split (J D : ℕ) (hD : D<2^J) :
    ∃ s : DigitSplit, s.leftCount*s.rightCount=2^J ∧ s.leftMax=D ∧ s.rightMax=2^J-1-D := by
  induction J generalizing D with
  | zero =>
    have : D=0 := by simpa using hD
    subst D
    exact ⟨DigitSplit.empty,rfl,rfl,rfl⟩
  | succ J ih =>
    rw [pow_succ] at hD ⊢
    obtain ⟨s,p,l,r⟩ := ih (D/2) (by omega)
    by_cases evenD : D%2=0
    · refine ⟨s.swap.doubleLeft.swap,?_,?_,?_⟩
      · change s.leftCount*(2*s.rightCount)=2^J*2
        rw [←p]; ring
      · change 2*s.leftMax=D
        omega
      · change 2*s.rightMax+1=2^J*2-1-D
        omega
    · refine ⟨s.doubleLeft,?_,?_,?_⟩
      · change 2*s.leftCount*s.rightCount=2^J*2
        rw [←p]; ring
      · change 2*s.leftMax+1=D
        omega
      · change 2*s.rightMax=2^J*2-1-D
        omega

end NathansonSidon
