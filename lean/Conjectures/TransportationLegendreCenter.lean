import Conjectures.TransportationLegendreODE
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Nat.Choose.Central

/-! The two parity cases at the center of Rodrigues' polynomials and an elementary
bound for their normalized central binomial coefficients. -/

namespace TransportationEhrhart

open Polynomial

noncomputable def centralAmplitude (k : ℕ) : ℝ := (1/4 : ℝ)^k*(k.centralBinom : ℝ)

theorem rodrigues_expand (n : ℕ) :
    rodriguesBase n=expand ℝ 2 ((X+C (-1 : ℝ))^n) := by
  simp [rodriguesBase,sub_eq_add_neg]

theorem rodrigues_even_coeff (n j : ℕ) :
    (rodriguesBase n).coeff (2*j)=(-1 : ℝ)^(n-j)*(n.choose j : ℝ) := by
  rw [rodrigues_expand,coeff_expand_mul' (by decide : 0<2),coeff_X_add_C_pow]

theorem rodrigues_odd_coeff (n j : ℕ) : (rodriguesBase n).coeff (2*j+1)=0 := by
  rw [rodrigues_expand,coeff_expand (by decide : 0<2),ite_eq_right (by omega)]

theorem legendre_coeff (n j : ℕ) : (legendre n).coeff j=
    (1/2 : ℝ)^n*((j+n).choose n : ℝ)*(rodriguesBase n).coeff (j+n) := by
  simp only [legendre,coeff_C_mul,hasseDeriv_coeff,mul_assoc]

theorem even_center (k : ℕ) :
    (legendre (2*k)).eval 0=(-1 : ℝ)^k*centralAmplitude k ∧
      (legendre (2*k)).derivative.eval 0=0 := by
  simp only [←coeff_zero_eq_eval_zero,coeff_derivative,Nat.cast_one,mul_one,legendre_coeff,
    zero_add,Nat.choose_self,Nat.add_comm 1 (2*k),rodrigues_even_coeff,rodrigues_odd_coeff,
    mul_zero]
  simp only [centralAmplitude,Nat.centralBinom_eq_two_mul_choose,
    show 2*k-k=k by omega,pow_mul]
  norm_num
  ring

theorem odd_center (k : ℕ) :
    (legendre (2*k+1)).eval 0=0 ∧
      (legendre (2*k+1)).derivative.eval 0=(-1 : ℝ)^k*((2*k+1 : ℕ) : ℝ)*centralAmplitude k := by
  have sym := Nat.choose_symm (show k≤2*k+1 by omega)
  rw [show 2*k+1-k=k+1 by omega] at sym
  have mult := Nat.choose_mul_succ_eq (2*k) k
  rw [show 2*k+1-k=k+1 by omega] at mult
  have m : ((2*k+1).choose (k+1) : ℝ)*(k+1)=(2*k+1 : ℝ)*k.centralBinom := by
    rw [sym,Nat.centralBinom_eq_two_mul_choose,mul_comm (2*(k : ℝ)+1)]
    exact_mod_cast mult.symm
  simp only [←coeff_zero_eq_eval_zero,coeff_derivative,legendre_coeff,
    zero_add,rodrigues_odd_coeff,mul_zero,true_and]
  rw [show 1+(2*k+1)=(2*k+1)+1 by omega,Nat.choose_succ_self_right,
    show 2*k+1+1=2*(k+1) by omega,rodrigues_even_coeff,show 2*k+1-(k+1)=k by omega]
  simp only [centralAmplitude,pow_succ (1/2 : ℝ) (2*k),pow_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    Nat.cast_ofNat]
  norm_num
  linear_combination (-1 : ℝ)^k*(1/4 : ℝ)^k*m

theorem central_step (k : ℕ) :
    (2*((k : ℝ)+1))*centralAmplitude (k+1)=(2*k+1)*centralAmplitude k := by
  have h : ((k : ℝ)+1)*((k+1).centralBinom : ℝ)=2*(2*k+1)*k.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  simp only [centralAmplitude,pow_succ]
  linear_combination ((1/4 : ℝ)^k/2)*h

theorem central_square_bound (k : ℕ) : ((k : ℝ)+1)*(centralAmplitude k)^2≤1 := by
  induction k with
  | zero => norm_num [centralAmplitude]
  | succ k ih =>
    have pos : 0<2*((k : ℝ)+1) := by positivity
    have eq : centralAmplitude (k+1)=(2*k+1)*centralAmplitude k/(2*((k : ℝ)+1)) :=
      (eq_div_iff pos.ne').2 (by rw [mul_comm]; exact central_step k)
    have bound : ((k : ℝ)+2)*(2*k+1)^2≤((k : ℝ)+1)*(2*(k+1))^2 := by
      nlinarith [sq_nonneg (k : ℝ),Nat.cast_nonneg (α := ℝ) k]
    rw [Nat.cast_succ,eq]
    calc
      _ = (((k : ℝ)+2)*(2*k+1)^2)*(centralAmplitude k)^2/(2*(k+1))^2 := by field_simp; ring
      _ ≤ (((k : ℝ)+1)*(2*(k+1))^2)*(centralAmplitude k)^2/(2*(k+1))^2 := by gcongr
      _ = ((k : ℝ)+1)*(centralAmplitude k)^2 := by field_simp
      _ ≤ 1 := ih

end TransportationEhrhart
