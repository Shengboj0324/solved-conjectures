import Conjectures.NathansonSidonDiameter
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.Basic

/-! Dividing out the common coefficient divisor preserves the representation
fibers and gives the sharp finite interval-counting upper bound. -/

namespace NathansonSidon

variable {h : ℕ}

def coefficientGcd (c : Fin h → ℤ) : ℕ := Finset.univ.gcd fun i => (c i).natAbs

theorem gcd_dvd_weight (c : Fin h → ℤ) (i : Fin h) : coefficientGcd c∣(c i).natAbs :=
  Finset.gcd_dvd (Finset.mem_univ i)

theorem coefficientGcd_pos (hh : 0<h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0) : 0<coefficientGcd c := by
  let i : Fin h := ⟨0,hh⟩
  have dv := gcd_dvd_weight c i
  exact Nat.pos_of_dvd_of_pos dv (Int.natAbs_pos.mpr (nz i))

theorem output_scale (k : ℤ) (b x : Fin h → ℤ) :
    output (fun i => k*b i) x=k*output b x := by
  simp only [output,Finset.mul_sum,mul_assoc]

theorem scale_fibers (k : ℤ) (hk : k≠0) (b : Fin h → ℤ) (A : Fin h → Finset ℤ) (z : ℤ) :
    representations (fun i => k*b i) A (k*z)=representations b A z := by
  simp only [representations,output_scale,mul_right_inj' hk]

theorem feasible_divide {N g q : ℕ} {c b : Fin h → ℤ} {k : ℤ}
    (hk : k≠0) (factor : ∀ i,k*b i=c i) (w : Feasible c N g q) : Feasible b N g q := by
  obtain ⟨A,sets,mult⟩ := w
  refine ⟨A,sets,fun z => ?_⟩
  rw [←scale_fibers k hk b A z]
  simpa only [factor] using mult (k*z)

theorem normalized_diameter {c : Fin h → ℤ} {N g q : ℕ} (hh : 0<h) (nz : ∀ i,c i≠0)
    (w : Feasible c N g q) : q^h≤g*((coefficientSum c/coefficientGcd c)*(N-1)+1) := by
  let D := coefficientGcd c
  let b := fun i => c i/(D : ℤ)
  have pos : 0<D := coefficientGcd_pos hh c nz
  have kpos : (D : ℤ)≠0 := by exact_mod_cast Nat.ne_of_gt pos
  have factor (i : Fin h) : (D : ℤ)*b i=c i :=
    Int.mul_ediv_cancel' (Int.natCast_dvd.mpr (gcd_dvd_weight c i))
  have single (i : Fin h) : D*(b i).natAbs=(c i).natAbs := by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using congrArg Int.natAbs (factor i)
  have total : D*coefficientSum b=coefficientSum c := by
    simp only [coefficientSum,Finset.mul_sum,single]
  have reduced : coefficientSum c/D=coefficientSum b := by
    rw [←total,Nat.mul_div_cancel_left _ pos]
  have bound := feasible_diameter hh (feasible_divide kpos factor w)
  simpa only [←reduced] using bound

theorem extremal_normalized_diameter (hh : 0<h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0) (N : ℕ) :
    (extremal c N 1)^h≤(coefficientSum c/coefficientGcd c)*(N-1)+1 := by
  simpa using normalized_diameter hh nz (extremal_feasible hh c N 1)

end NathansonSidon
