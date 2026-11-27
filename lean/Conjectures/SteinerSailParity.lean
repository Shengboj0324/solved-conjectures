import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! The parity witness for two disjoint blocks and the numerical deduction
of the sail bound from its incidence and variance estimates. -/

namespace SteinerSail

private theorem allEven {ι : Type*} (s : Finset ι) (v : ι → ℕ) (even : ∀ i∈s,Even (v i)) :
    Even (∑ i∈s,v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (even i (Finset.mem_insert_self _ _)).add (ih (fun j hj => even j (Finset.mem_insert_of_mem hj)))

theorem opposite_array {X Y : Type*} [Fintype X] [Fintype Y]
    (hx : Odd (Fintype.card X)) (hy : Odd (Fintype.card Y)) (red : X → Y → Bool) :
    (∃ x,Odd (∑ y : Y,if red x y then (1 : ℕ) else 0)) ∨
    (∃ y,Odd (∑ x : X,if red x y then (0 : ℕ) else 1)) := by
  classical
  by_contra! bad
  have rr : Even (∑ x : X,∑ y : Y,if red x y then (1 : ℕ) else 0) := by
    apply allEven
    intro x _
    exact Nat.not_odd_iff_even.mp (bad.1 x)
  have bb : Even (∑ y : Y,∑ x : X,if red x y then (0 : ℕ) else 1) := by
    apply allEven
    intro y _
    exact Nat.not_odd_iff_even.mp (bad.2 y)
  have total := rr.add bb
  rw [Finset.sum_comm (f := fun y x => if red x y then (0 : ℕ) else 1),←Finset.sum_add_distrib] at total
  have row (x : X) :
      (∑ y,if red x y then (1 : ℕ) else 0)+(∑ y,if red x y then (0 : ℕ) else 1)=Fintype.card Y := by
    rw [←Finset.sum_add_distrib]
    have term (y : Y) : (if red x y then (1 : ℕ) else 0) + (if red x y then 0 else 1) = 1 := by
      cases red x y <;> decide
    simp only [term,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
  simp only [row,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at total
  exact (Nat.not_odd_iff_even.mpr total) (hx.mul hy)

theorem spoke_identity {j : ℕ} (hj : j≤3) :
    j+(if j=1 then 1 else 0)=j*(3-j)+3*(if j=3 then 1 else 0) := by
  interval_cases j <;> decide

theorem sail_bound_of_counts {n L S D r b : ℝ} (hn : 1≤n) (hs : 0≤S) (hd : 0≤D)
    (oddCount : 2*S=6*L+2*n*(n-1)-D)
    (opposite : 16*(r*b)≤n*(n-1)^2+8*(n-1)*(S+L))
    (blocks : 6*(r+b)=n*(n-1)) (spread : 36*(r-b)^2≤n*D) :
    n*(n-1)*(n*(n-3)-81*(n-1))≤(294*n-288)*L := by
  have hn0 : 0≤n := by linarith
  have su : S≤3*L+n*(n-1) := by linarith
  have du : D≤6*L+2*n*(n-1) := by linarith
  have prod := mul_le_mul_of_nonneg_left su (show 0≤8*(n-1) by linarith)
  have ub : 16*(r*b)≤9*n*(n-1)^2+32*(n-1)*L := by nlinarith only [opposite,prod]
  have sq := congrArg (fun x : ℝ => x^2) blocks
  have ld := spread.trans (mul_le_mul_of_nonneg_left du hn0)
  have lb : n^2*(n-1)*(n-3)-6*n*L≤144*(r*b) := by nlinarith only [sq,ld]
  nlinarith only [ub,lb]

theorem positive_from_84 {n L : ℝ} (hn : 84≤n)
    (bound : n*(n-1)*(n*(n-3)-81*(n-1))≤(294*n-288)*L) : 0<L := by
  have factor : 0<n*(n-3)-81*(n-1) := by
    nlinarith only [mul_nonneg (by linarith : 0≤n) (by linarith : 0≤n-84)]
  have positive : 0<n*(n-1)*(n*(n-3)-81*(n-1)) :=
    mul_pos (mul_pos (by linarith) (by linarith)) factor
  exact pos_of_mul_pos_right (positive.trans_le bound) (by linarith)

end SteinerSail
