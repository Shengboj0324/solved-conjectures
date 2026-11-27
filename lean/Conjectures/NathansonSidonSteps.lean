import Conjectures.NathansonSidonProgressions
import Mathlib.Algebra.GCDMonoid.Finset

/-! Divisibility by the coefficients makes all the adjusted place values
integral. The last place gives the largest step when the base is large enough. -/

namespace NathansonSidon

def firstIndex {h : ℕ} (hh : 0<h) : Fin h := ⟨0,hh⟩
def lastIndex {h : ℕ} (hh : 0<h) : Fin h := ⟨h-1,by omega⟩

def period {h : ℕ} (c : Fin h → ℤ) := Finset.univ.lcm fun i => (c i).natAbs

def step {h : ℕ} (c : Fin h → ℤ) (u r : ℕ) (i : Fin h) := u*r^i.val/(c i).natAbs

theorem period_pos {h : ℕ} (c : Fin h → ℤ) (nz : ∀ i,c i≠0) : 0<period c := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr fun i _ => Int.natAbs_ne_zero.mpr (nz i)

theorem weight_step {h r : ℕ} (hh : 0<h) (c : Fin h → ℤ) (multi : period c∣r) (i : Fin h) :
    let u := (c (firstIndex hh)).natAbs
    (c i).natAbs*step c u r i=u*r^i.val := by
  dsimp only [step]
  rw [Nat.mul_comm,Nat.div_mul_cancel]
  by_cases z : i.val=0
  · have e : i=firstIndex hh := Fin.ext z
    simp [e,firstIndex]
  · have dvd : (c i).natAbs∣period c := Finset.dvd_lcm (Finset.mem_univ i)
    exact dvd_mul_of_dvd_right ((dvd.trans multi).trans (dvd_pow_self _ z)) _

theorem largest_step {h r : ℕ} (hh : 0<h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0) (hr : 0<r)
    (multi : period c∣r) (least : ∀ i,(c (firstIndex hh)).natAbs≤(c i).natAbs)
    (large : (c (lastIndex hh)).natAbs≤(c (firstIndex hh)).natAbs*r) (i : Fin h) :
    let u := (c (firstIndex hh)).natAbs
    step c u r i≤step c u r (lastIndex hh) := by
  let v := (c (lastIndex hh)).natAbs
  let u := (c (firstIndex hh)).natAbs
  dsimp only
  by_cases final : i=lastIndex hh
  · rw [final]
  · have small : i.val+1≤(lastIndex hh).val := by
      have ne : i.val≠(lastIndex hh).val := fun e => final (Fin.ext e)
      dsimp [lastIndex] at ne ⊢; have := i.isLt; omega
    have comp : v≤(c i).natAbs*r := le_trans large (Nat.mul_le_mul_right r (least i))
    have bound : v*step c u r i ≤ v*step c u r (lastIndex hh) := calc
      _ ≤ ((c i).natAbs*r)*step c u r i := Nat.mul_le_mul_right _ comp
      _ = ((c i).natAbs*step c u r i)*r := by ring
      _ = (u*r^i.val)*r := by rw [weight_step hh c multi i]
      _ = u*r^(i.val+1) := by rw [pow_succ]; ring
      _ ≤ u*r^(lastIndex hh).val := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hr small)
      _ = _ := (weight_step hh c multi (lastIndex hh)).symm
    exact Nat.le_of_mul_le_mul_left bound (Int.natAbs_pos.mpr (nz _))

theorem finite_system {h r N : ℕ} (hh : 0<h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0) (hr : 0<r)
    (multi : period c∣r) (least : ∀ i,(c (firstIndex hh)).natAbs≤(c i).natAbs)
    (large : (c (lastIndex hh)).natAbs≤(c (firstIndex hh)).natAbs*r)
    (room : (c (firstIndex hh)).natAbs*r^h≤(c (lastIndex hh)).natAbs*(N-1)) :
    Feasible c N 1 r := by
  let u := (c (firstIndex hh)).natAbs
  let v := (c (lastIndex hh)).natAbs
  have hu : 0<u := Int.natAbs_pos.mpr (nz _)
  have hv : 0<v := Int.natAbs_pos.mpr (nz _)
  have hs (i : Fin h) : 0<step c u r i := by
    have eq := weight_step hh c multi i
    have big := Nat.mul_pos hu (pow_pos hr i.val)
    change (c i).natAbs*step c u r i=u*r^i.val at eq
    rw [←eq] at big
    exact Nat.pos_of_mul_pos_left big
  apply positional_feasible c (step c u r) hu hs (weight_step hh c multi)
  intro i
  have t := largest_step hh c nz hr multi least large i
  have last : v*step c u r (lastIndex hh)*r=u*r^h := by
    rw [show v*step c u r (lastIndex hh)=u*r^(h-1) from weight_step hh c multi _]
    rw [mul_assoc,←pow_succ,show h-1+1=h by omega]
  have bound : v*(step c u r i*(r-1))≤v*(N-1) := calc
    _ ≤ v*(step c u r (lastIndex hh)*r) := Nat.mul_le_mul_left _ (Nat.mul_le_mul t (by omega))
    _ = u*r^h := by rw [←mul_assoc,last]
    _ ≤ _ := room
  have lower := Nat.le_of_mul_le_mul_left bound hv
  have Npos : 0<N := by
    by_contra! zero
    have zn : N=0 := by omega
    rw [zn] at room
    have up := Nat.mul_pos hu (pow_pos hr h)
    change u*r^h≤v*(0-1) at room
    simp at room
    omega
  omega

end NathansonSidon
