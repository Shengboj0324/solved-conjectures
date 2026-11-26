import Conjectures.TransportationLegendreODE
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! A decreasing energy for the Legendre equation on the positive half of its interval. -/

namespace TransportationEhrhart

open Polynomial Set

noncomputable def legendreGap (x : ℝ) := 1-x^2
noncomputable def legendreMass (n : ℕ) := (n : ℝ)*(n+1)
noncomputable def legendreWeight (n : ℕ) := 4*legendreMass n+1
noncomputable def legendreDen (n : ℕ) (x : ℝ) := legendreWeight n*legendreGap x+1
noncomputable def legendreMomentum (n : ℕ) (x : ℝ) :=
  2*legendreGap x*(legendre n).derivative.eval x-x*(legendre n).eval x
noncomputable def legendreEnergy (n : ℕ) (x : ℝ) :=
  Real.sqrt (legendreGap x)*((legendre n).eval x^2+legendreMomentum n x^2/legendreDen n x)

theorem legendre_ode_eval (n : ℕ) (x : ℝ) :
    legendreGap x*(legendre n).derivative.derivative.eval x=
      2*x*(legendre n).derivative.eval x-legendreMass n*(legendre n).eval x := by
  have h := congrArg (eval x) (legendre_ode n)
  simp only [eval_add,eval_mul,eval_sub,eval_pow,eval_X,eval_one,eval_ofNat,eval_natCast] at h
  unfold legendreGap legendreMass
  linear_combination -h

theorem legendre_gap_deriv (x : ℝ) : HasDerivAt legendreGap (-2*x) x := by
  apply ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).congr_deriv
  simp

theorem legendre_den_pos (n : ℕ) {x : ℝ} (h : 0≤legendreGap x) : 0<legendreDen n x := by
  unfold legendreDen legendreWeight legendreMass
  positivity

theorem legendre_den_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (legendreDen n) (-2*legendreWeight n*x) x := by
  apply (((legendre_gap_deriv x).const_mul (legendreWeight n)).add_const 1).congr_deriv
  ring

theorem legendre_momentum_deriv (n : ℕ) (x : ℝ) : HasDerivAt (legendreMomentum n)
    (-x*(legendre n).derivative.eval x-(2*legendreMass n+1)*(legendre n).eval x) x := by
  let p := legendre n
  have h := (((legendre_gap_deriv x).const_mul 2).mul (p.derivative.hasDerivAt x)).sub
    ((hasDerivAt_id x).mul (p.hasDerivAt x))
  apply h.congr_deriv
  dsimp [p]
  linear_combination 2*legendre_ode_eval n x

theorem legendre_energy_identity {x c y d r : ℝ} (hr : r^2=1-x^2) (nr : r≠0) :
    let s:=1-x^2
    let a:=4*c+1
    let w:=2*s*d-x*y
    let q:=a*s+1
    q≠0 → (-x/r)*(y^2+w^2/q)+r*(2*y*d+((2*w*(-x*d-(2*c+1)*y))*q-w^2*(-2*a*x))/q^2)=
      -2*x*w^2/(r*q^2) := by
  intro s a w q nq
  calc
    _ = ((-x)*(y^2*q^2+w^2*q)+r^2*(2*y*d*q^2+2*w*(-x*d-(2*c+1)*y)*q-w^2*(-2*a*x)))/
        (r*q^2) := by field_simp; ring
    _ = _ := by
      congr 1
      rw [hr]
      dsimp [s,a,w,q]
      ring

theorem legendre_energy_deriv (n : ℕ) {x : ℝ} (h : 0<legendreGap x) :
    HasDerivAt (legendreEnergy n)
      (-2*x*legendreMomentum n x^2/(Real.sqrt (legendreGap x)*legendreDen n x^2)) x := by
  let p:=legendre n
  let r:=Real.sqrt (legendreGap x)
  have hr : r^2=1-x^2 := Real.sq_sqrt h.le
  have nr : r≠0 := (Real.sqrt_pos.2 h).ne'
  have nq := (legendre_den_pos n h.le).ne'
  have root : HasDerivAt (fun z => Real.sqrt (legendreGap z)) (-x/r) x := by
    apply ((legendre_gap_deriv x).sqrt h.ne').congr_deriv
    change -2*x/(2*r) = -x/r
    field_simp
  have full := root.mul (((p.hasDerivAt x).pow 2).add
    (((legendre_momentum_deriv n x).pow 2).div (legendre_den_deriv n x) nq))
  apply full.congr_deriv
  simpa only [p,r,Pi.add_apply,Pi.div_apply,Pi.pow_apply,legendreMomentum,legendreDen,
    legendreWeight,legendreGap,Nat.cast_ofNat,Nat.reduceSub,pow_one] using
    legendre_energy_identity (c := legendreMass n) (y := (legendre n).eval x)
      (d := (legendre n).derivative.eval x) hr nr nq

theorem legendre_energy_le_center (n : ℕ) {x : ℝ} (hx : 0≤x) (h1 : x<1) :
    legendreEnergy n x≤legendreEnergy n 0 := by
  have hgap (z : ℝ) (hz : z∈Icc 0 x) : 0<legendreGap z := by
    have hz1:=hz.2.trans_lt h1
    unfold legendreGap
    nlinarith [mul_pos (sub_pos.mpr hz1) (by linarith [hz.1] : 0<1+z)]
  have cont : ContinuousOn (legendreEnergy n) (Icc 0 x) := fun z hz =>
    (legendre_energy_deriv n (hgap z hz)).continuousAt.continuousWithinAt
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 x) cont _ _ (left_mem_Icc.mpr hx) (right_mem_Icc.mpr hx) hx
  · exact fun z hz => (legendre_energy_deriv n (hgap z (interior_subset hz))).differentiableAt.differentiableWithinAt
  · intro z hz
    have hz0:= (interior_subset hz : z∈Icc 0 x)
    rw [(legendre_energy_deriv n (hgap z hz0)).deriv]
    have hz' := hz0.1
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    · positivity

end TransportationEhrhart
