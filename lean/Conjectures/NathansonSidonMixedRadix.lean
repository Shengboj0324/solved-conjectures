import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Unequal coordinate radices. The last coordinate can occupy the full
middle range, while every earlier one is smaller by its radix factor. -/

namespace NathansonSidon

def mixedPack : {h : ℕ} → (Fin h → ℕ) → (Fin h → ℕ) → ℕ
  | 0, _, _ => 0
  | _+1, r, x => x 0+r 0*mixedPack (Fin.tail r) (Fin.tail x)

def mixedStride : {h : ℕ} → (Fin h → ℕ) → Fin h → ℕ
  | 0, _ => Fin.elim0
  | _+1, r => Fin.cons 1 fun i => r 0*mixedStride (Fin.tail r) i

theorem mixedPack_eq_sum {h : ℕ} (r x : Fin h → ℕ) :
    mixedPack r x=∑ i,mixedStride r i*x i := by
  induction h with
  | zero => simp [mixedPack]
  | succ h ih =>
    rw [Fin.sum_univ_succ,mixedPack,ih,Finset.mul_sum]
    simp only [mixedStride,Fin.cons_zero,Fin.cons_succ,one_mul,Fin.tail,mul_assoc]

theorem mixedPack_lt {h : ℕ} (r x : Fin h → ℕ) (hx : ∀ i,x i<r i) :
    mixedPack r x<∏ i,r i := by
  induction h with
  | zero => simp [mixedPack]
  | succ h ih =>
    rw [Fin.prod_univ_succ,mixedPack]
    have bound := ih (Fin.tail r) (Fin.tail x) (fun i => hx i.succ)
    calc
      x 0+r 0*mixedPack (Fin.tail r) (Fin.tail x)
          < r 0*(mixedPack (Fin.tail r) (Fin.tail x)+1) := by
            rw [Nat.mul_add,Nat.mul_one]
            have := hx 0
            omega
      _ ≤ _ := Nat.mul_le_mul_left _ bound

theorem mixedPack_unique {h : ℕ} (r x y : Fin h → ℕ)
    (hx : ∀ i,x i<r i) (hy : ∀ i,y i<r i) (eq : mixedPack r x=mixedPack r y) : x=y := by
  induction h with
  | zero => funext i; exact Fin.elim0 i
  | succ h ih =>
    rw [mixedPack,mixedPack] at eq
    have modEq := congrArg (fun t => t%r 0) eq
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (hx 0),Nat.mod_eq_of_lt (hy 0)] at modEq
    rw [modEq] at eq
    have rest := ih (Fin.tail r) (Fin.tail x) (Fin.tail y) (fun i => hx i.succ) (fun i => hy i.succ)
      (Nat.eq_of_mul_eq_mul_left (by have := hx 0; omega) (Nat.add_left_cancel eq))
    funext i
    exact Fin.cases modEq (fun j => congrFun rest j) i

theorem mixedStride_before {h : ℕ} (r : Fin h → ℕ) (hr : ∀ i,0<r i)
    (i j : Fin h) (hij : i<j) : mixedStride r i*r i*r j≤∏ k,r k := by
  induction h with
  | zero => exact Fin.elim0 i
  | succ h ih =>
    rw [Fin.prod_univ_succ]
    refine Fin.cases (motive := fun i => i<j → mixedStride r i*r i*r j≤_)
      (fun hj => ?_) (fun a haj => ?_) i hij
    · obtain ⟨b,rfl⟩ := Fin.exists_succ_eq_of_ne_zero (Fin.ne_of_gt hj)
      change 1*r 0*r b.succ≤_
      rw [one_mul]
      apply Nat.mul_le_mul_left
      exact Finset.single_le_prod (f := Fin.tail r) (fun t _ => hr t.succ) (Finset.mem_univ b)
    · obtain ⟨b,rfl⟩ := Fin.exists_succ_eq_of_ne_zero (Fin.ne_of_gt (Fin.zero_le a.succ |>.trans_lt haj))
      have bound := ih (Fin.tail r) (fun t => hr t.succ) a b (Fin.succ_lt_succ_iff.mp haj)
      change (r 0*mixedStride (Fin.tail r) a)*r a.succ*r b.succ≤_
      simpa only [Fin.tail,mul_assoc] using Nat.mul_le_mul_left (r 0) bound

end NathansonSidon
