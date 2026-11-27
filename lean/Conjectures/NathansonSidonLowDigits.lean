import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-! The low digits of a weighted Sidon system. Successive gcds give a
rectangular set of digits with pairwise distinct weighted residues. -/

namespace NathansonSidon

def lowGcd (m : ℕ) : {h : ℕ} → (Fin h → ℕ) → ℕ
  | 0, _ => m
  | _+1, b => (lowGcd m (Fin.tail b)).gcd (b 0)

def lowRadix (m : ℕ) : {h : ℕ} → (Fin h → ℕ) → Fin h → ℕ
  | 0, _ => Fin.elim0
  | _+1, b => Fin.cons (lowGcd m (Fin.tail b)/lowGcd m b) (lowRadix m (Fin.tail b))

def lowOutput {h : ℕ} (b d : Fin h → ℕ) : ℕ := ∑ i,b i*d i

theorem lowGcd_dvd_modulus {h : ℕ} (m : ℕ) (b : Fin h → ℕ) : lowGcd m b∣m := by
  induction h with
  | zero => rfl
  | succ h ih => exact (Nat.gcd_dvd_left _ _).trans (ih (Fin.tail b))

theorem lowGcd_pos {h m : ℕ} (hm : 0<m) (b : Fin h → ℕ) : 0<lowGcd m b :=
  Nat.pos_of_dvd_of_pos (lowGcd_dvd_modulus m b) hm

theorem lowGcd_dvd_weight {h : ℕ} (m : ℕ) (b : Fin h → ℕ) (i : Fin h) : lowGcd m b∣b i := by
  induction h with
  | zero => exact Fin.elim0 i
  | succ h ih =>
    refine Fin.cases (Nat.gcd_dvd_right _ _) (fun j => ?_) i
    exact (Nat.gcd_dvd_left _ _).trans (ih (Fin.tail b) j)

theorem dvd_lowGcd {h m a : ℕ} (b : Fin h → ℕ) (hm : a∣m) (hb : ∀ i,a∣b i) :
    a∣lowGcd m b := by
  induction h with
  | zero => exact hm
  | succ h ih => exact Nat.dvd_gcd (ih (Fin.tail b) fun i => hb i.succ) (hb 0)

theorem lowGcd_eq_gcd {h m : ℕ} (b : Fin h → ℕ) :
    lowGcd m b=m.gcd (Finset.univ.gcd b) := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (lowGcd_dvd_modulus _ _) (Finset.dvd_gcd fun i _ => lowGcd_dvd_weight _ _ i)
  · exact dvd_lowGcd b (Nat.gcd_dvd_left _ _)
      (fun i => (Nat.gcd_dvd_right _ _).trans (Finset.gcd_dvd (Finset.mem_univ i)))

theorem lowRadix_product {h : ℕ} (m : ℕ) (b : Fin h → ℕ) :
    (∏ i,lowRadix m b i)*lowGcd m b=m := by
  induction h with
  | zero => simp [lowGcd]
  | succ h ih =>
    rw [Fin.prod_univ_succ]
    change (lowGcd m (Fin.tail b)/lowGcd m b)*(∏ i,lowRadix m (Fin.tail b) i)*lowGcd m b=m
    have dv : lowGcd m b∣lowGcd m (Fin.tail b) := Nat.gcd_dvd_left _ _
    rw [mul_right_comm,Nat.div_mul_cancel dv,mul_comm]
    exact ih (Fin.tail b)

theorem lowOutput_succ {h : ℕ} (b d : Fin (h+1) → ℕ) :
    lowOutput b d=b 0*d 0+lowOutput (Fin.tail b) (Fin.tail d) :=
  Fin.sum_univ_succ _

theorem lowGcd_dvd_output {h : ℕ} (m : ℕ) (b d : Fin h → ℕ) : lowGcd m b∣lowOutput b d :=
  Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left (lowGcd_dvd_weight m b i) _

theorem lowDigits_unique {h m : ℕ} (hm : 0<m) (b x y : Fin h → ℕ)
    (hx : ∀ i,x i<lowRadix m b i) (hy : ∀ i,y i<lowRadix m b i)
    (eq : lowOutput b x ≡ lowOutput b y [MOD m]) : x=y := by
  induction h with
  | zero => funext i; exact Fin.elim0 i
  | succ h ih =>
    rw [lowOutput_succ,lowOutput_succ] at eq
    let g := lowGcd m (Fin.tail b)
    have tailEq : lowOutput (Fin.tail b) (Fin.tail x) ≡ lowOutput (Fin.tail b) (Fin.tail y) [MOD g] :=
      (lowGcd_dvd_output m _ _).modEq_zero_nat.trans (lowGcd_dvd_output m _ _).zero_modEq_nat
    have lead : b 0*x 0 ≡ b 0*y 0 [MOD g] :=
      tailEq.add_right_cancel (eq.of_dvd (lowGcd_dvd_modulus m _))
    have first : x 0=y 0 :=
      (lead.cancel_left_div_gcd (lowGcd_pos hm _)).eq_of_lt_of_lt (hx 0) (hy 0)
    rw [first] at eq
    have rest := ih (Fin.tail b) (Fin.tail x) (Fin.tail y)
      (fun i => hx i.succ) (fun i => hy i.succ) (Nat.ModEq.add_left_cancel' _ eq)
    funext i
    exact Fin.cases first (fun j => congrFun rest j) i

end NathansonSidon
