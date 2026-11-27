import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Packing signed-form coordinate digits first requires the ordinary
bijection from bounded digit tuples to the entire base-r interval. -/

namespace NathansonSidon

def pack {h r : ℕ} (d : Fin h → Fin r) : ℕ := ∑ i,r^i.val*(d i).val

theorem pack_succ {h r : ℕ} (d : Fin (h+1) → Fin r) :
    pack d=(d 0).val+r*pack (fun i => d i.succ) := by
  simp only [pack,Fin.sum_univ_succ,Fin.val_zero,pow_zero,one_mul,Fin.val_succ,pow_succ,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pack_lt {r h : ℕ} (d : Fin h → Fin r) : pack d<r^h := by
  induction h with
  | zero => simp [pack]
  | succ h ih =>
    have tail := ih (fun i => d i.succ)
    have bound := Nat.mul_le_mul_left r (Nat.succ_le_of_lt tail)
    rw [pack_succ,pow_succ]
    have hd := (d 0).isLt
    nlinarith

theorem pack_injective {r h : ℕ} (hr : 0<r) : Function.Injective (@pack h r) := by
  induction h with
  | zero => intro x y _; exact Subsingleton.elim _ _
  | succ h ih =>
    intro x y eq
    rw [pack_succ,pack_succ] at eq
    have units := congrArg (· % r) eq
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (x 0).isLt,Nat.mod_eq_of_lt (y 0).isLt] at units
    have same : x 0=y 0 := Fin.ext units
    have tails : pack (fun i => x i.succ) = pack (fun i => y i.succ) := by
      rw [same] at eq
      exact Nat.eq_of_mul_eq_mul_left hr (Nat.add_left_cancel eq)
    have e := ih tails
    funext i
    exact Fin.cases same (fun j => congrFun e j) i

theorem pack_surjective {r : ℕ} (hr : 0<r) (h n : ℕ) (hn : n<r^h) :
    ∃ d : Fin h → Fin r,pack d=n := by
  induction h generalizing n with
  | zero => exact ⟨Fin.elim0,by simp [pack]; symm; simpa using hn⟩
  | succ h ih =>
    have hd : n/r<r^h := (Nat.div_lt_iff_lt_mul hr).mpr (by simpa [pow_succ] using hn)
    obtain ⟨tail,eq⟩ := ih _ hd
    let d : Fin (h+1) → Fin r := Fin.cases ⟨n%r,Nat.mod_lt _ hr⟩ tail
    refine ⟨d,?_⟩
    rw [pack_succ]
    change n%r+r*pack tail=n
    rw [eq,Nat.mod_add_div]

end NathansonSidon
