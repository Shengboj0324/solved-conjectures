import Conjectures.TransportationLegendreODE
import Conjectures.TransportationPolynomial
import Mathlib.Algebra.Polynomial.Taylor

/-! The Möbius substitution relating the binomial numerator to Rodrigues' polynomials. -/

namespace TransportationEhrhart

open Polynomial

noncomputable def binomialSquare (m : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (m+1), C ((m.choose j : ℝ)^2) * X^j

theorem numerator_linear (m : ℕ) : numerator m=binomialSquare m-C (m : ℝ)*X := rfl

theorem taylor_rodrigues (m : ℕ) (x : ℝ) :
    taylor x (rodriguesBase m)=(X+C (x+1))^m*(X+C (x-1))^m := by
  rw [rodriguesBase,show (X^2-1 : ℝ[X])=(X+1)*(X-1) by ring,mul_pow,taylor_mul,taylor_pow,taylor_pow]
  simp only [map_add,map_sub,taylor_X,taylor_one,C_1]
  ring

theorem legendre_expansion (m : ℕ) (x : ℝ) :
    (legendre m).eval x=(1/2 : ℝ)^m*
      ∑ j ∈ Finset.range (m+1), (m.choose j : ℝ)^2*(x-1)^j*(x+1)^(m-j) := by
  rw [legendre,eval_mul,eval_C,←taylor_coeff,taylor_rodrigues,coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have le : j≤m := by simpa using Finset.mem_range.mp hj
  simp only [coeff_X_add_C_pow,Nat.sub_sub_self le,Nat.choose_symm le]
  ring

noncomputable def legendreCoordinate (z : ℝ) := (1-z)/(1+z)

theorem binomialSquare_transform (m : ℕ) {z : ℝ} (hz : 0≤z) :
    (binomialSquare m).eval (-z)=(1+z)^m*(legendre m).eval (legendreCoordinate z) := by
  have nz : 1+z≠0 := by positivity
  let a := (1+z)*(1/2)
  have hm : a*(legendreCoordinate z-1) = -z := by
    dsimp [a,legendreCoordinate]
    field_simp
    ring
  have hp : a*(legendreCoordinate z+1) = 1 := by
    dsimp [a,legendreCoordinate]
    field_simp
    ring
  rw [legendre_expansion,←mul_assoc,←mul_pow,Finset.mul_sum]
  simp only [binomialSquare,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
  apply Finset.sum_congr rfl
  intro j hj
  have le : j≤m := by simpa using Finset.mem_range.mp hj
  change (m.choose j : ℝ)^2*(-z)^j=a^m*((m.choose j : ℝ)^2*
    (legendreCoordinate z-1)^j*(legendreCoordinate z+1)^(m-j))
  calc
    _ = (m.choose j : ℝ)^2*(a*(legendreCoordinate z-1))^j*
        (a*(legendreCoordinate z+1))^(m-j) := by rw [hm,hp,one_pow,mul_one]
    _ = _ := by
      rw [mul_pow a (legendreCoordinate z-1),mul_pow a (legendreCoordinate z+1),
        show a^m=a^j*a^(m-j) by rw [←pow_add,Nat.add_sub_of_le le]]
      ring

end TransportationEhrhart
