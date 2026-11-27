import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Tactic

/-! Rodrigues' polynomials and the Legendre differential equation. -/

namespace TransportationEhrhart

open Polynomial

noncomputable abbrev jet (n : ℕ) (p : ℝ[X]) := derivative^[n] p

theorem jet_succ (n : ℕ) (p : ℝ[X]) : jet (n+1) p=(jet n p).derivative :=
  Function.iterate_succ_apply' _ _ _

theorem jet_derivative (n : ℕ) (p : ℝ[X]) : jet n p.derivative=jet (n+1) p := rfl

theorem jet_mul_x (n : ℕ) (p : ℝ[X]) :
    jet (n+1) (X*p)=X*jet (n+1) p + ((n+1 : ℕ) : ℝ[X])*jet n p := by
  have h := iterate_derivative_mul_X (n := n+1) p
  simpa only [jet,Nat.add_one_sub_one,nsmul_eq_mul,mul_comm X] using h

theorem jet_sub (n : ℕ) (p q : ℝ[X]) : jet n (p-q)=jet n p-jet n q := by
  induction n with
  | zero => rfl
  | succ n ih => rw [jet_succ,ih,map_sub,←jet_succ,←jet_succ]

theorem jet_mul_quadratic (n : ℕ) (p : ℝ[X]) :
    jet (n+2) ((X^2-1)*p)=(X^2-1)*jet (n+2) p+
      (2*(n+2 : ℕ) : ℝ[X])*X*jet (n+1) p+((n+2 : ℕ)*(n+1 : ℕ) : ℝ[X])*jet n p := by
  rw [show (X^2-1)*p=X*(X*p)-p by ring,jet_sub,jet_mul_x (n+1) (X*p),jet_mul_x (n+1) p,jet_mul_x n p]
  push_cast
  ring

noncomputable def rodriguesBase (n : ℕ) : ℝ[X] := (X^2-1)^n
noncomputable def legendre (n : ℕ) : ℝ[X] := C ((1/2 : ℝ)^n) * hasseDeriv n (rodriguesBase n)

theorem base_derivative (n : ℕ) :
    (X^2-1)*(rodriguesBase n).derivative=(2*n : ℝ[X])*(X*rodriguesBase n) := by
  cases n with
  | zero => simp [rodriguesBase]
  | succ n =>
    change (X^2-1)*derivative ((X^2-1)^(n+1))=_
    rw [derivative_pow,Nat.add_one_sub_one,map_sub,derivative_X_sq,derivative_one,sub_zero,C_ofNat,C_eq_natCast]
    simp only [rodriguesBase,pow_succ,Nat.cast_succ]
    ring

theorem jet_legendre_ode (n : ℕ) :
    let p:=jet n (rodriguesBase n)
    (X^2-1)*p.derivative.derivative+2*X*p.derivative=(n*(n+1) : ℝ[X])*p := by
  cases n with
  | zero => simp [jet,rodriguesBase]
  | succ n =>
    let g := rodriguesBase (n+1)
    have raw := congrArg (jet (n+2)) (base_derivative (n+1))
    change jet (n+2) ((X^2-1)*g.derivative)=jet (n+2) ((2*(n+1 : ℕ) : ℝ[X])*(X*g)) at raw
    rw [jet_mul_quadratic] at raw
    have scale : (2*(n+1 : ℕ) : ℝ[X])=((2*(n+1) : ℕ) : ℝ[X]) := by push_cast; rfl
    rw [scale,show jet (n+2) (((2*(n+1) : ℕ) : ℝ[X])*(X*g))=
      ((2*(n+1) : ℕ) : ℝ[X])*jet (n+2) (X*g) from iterate_derivative_natCast_mul,
      jet_mul_x (n+1)] at raw
    simp only [jet_derivative,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at raw
    change (X^2-1)*(jet (n+1) g).derivative.derivative+2*X*(jet (n+1) g).derivative=
      (((n+1 : ℕ) : ℝ[X])*(((n+1 : ℕ) : ℝ[X])+1))*jet (n+1) g
    simp only [←jet_succ,Nat.cast_succ]
    linear_combination raw

theorem legendre_as_jet (n : ℕ) :
    legendre n=C (((1/2 : ℝ)^n)/(n.factorial : ℝ))*jet n (rodriguesBase n) := by
  have fact := congrFun (factorial_smul_hasseDeriv (R := ℝ) (k := n)) (rodriguesBase n)
  change n.factorial • hasseDeriv n (rodriguesBase n)=jet n (rodriguesBase n) at fact
  rw [legendre,←fact,nsmul_eq_mul]
  have nz : (n.factorial : ℝ)≠0 := by positivity
  rw [←C_eq_natCast,←mul_assoc,←map_mul,div_mul_cancel₀ _ nz]

theorem legendre_ode (n : ℕ) :
    (X^2-1)*(legendre n).derivative.derivative+2*X*(legendre n).derivative=
      (n*(n+1) : ℝ[X])*(legendre n) := by
  rw [legendre_as_jet]
  simp only [derivative_C_mul]
  have h := jet_legendre_ode n
  dsimp only at h
  linear_combination C (((1/2 : ℝ)^n)/(n.factorial : ℝ))*h

end TransportationEhrhart
