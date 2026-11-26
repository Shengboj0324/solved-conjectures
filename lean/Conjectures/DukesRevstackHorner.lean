import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Homogeneous integer Horner evaluation certifies polynomial signs at exact
rational endpoints without any floating-point arithmetic. -/

open Polynomial

namespace DukesRevstack

noncomputable def polynomialOfRow : List ℤ → ℝ[X]
  | [] => 0
  | a::as => C (a : ℝ)+X*polynomialOfRow as

def scaledValue (u v : ℤ) : List ℤ → ℤ × ℤ
  | [] => (0,1)
  | a::as =>
    let tail := scaledValue u v as
    (v*a*tail.2+u*tail.1,v*tail.2)

theorem scaledValue_power (u v : ℤ) (c : List ℤ) :
    (scaledValue u v c).2=v^c.length := by
  induction c with
  | nil => simp [scaledValue]
  | cons a c ih => simp [scaledValue,ih,pow_succ,mul_comm]

theorem scaledValue_correct (u v : ℤ) (hv : v≠0) (c : List ℤ) :
    ((scaledValue u v c).1 : ℝ)=(v : ℝ)^c.length*(polynomialOfRow c).eval ((u : ℝ)/v) := by
  have nv : (v : ℝ)≠0 := by exact_mod_cast hv
  induction c with
  | nil => simp [scaledValue,polynomialOfRow]
  | cons a c ih =>
    simp only [scaledValue,polynomialOfRow,List.length_cons,Polynomial.eval_add,
      Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,Int.cast_add,Int.cast_mul,
      scaledValue_power,Int.cast_pow,ih,pow_succ]
    field_simp

theorem opposite_signs_of_scaled (c : List ℤ) (u₁ v₁ u₂ v₂ : ℤ)
    (v₁pos : 0<v₁) (v₂pos : 0<v₂)
    (opposite : (scaledValue u₁ v₁ c).1*(scaledValue u₂ v₂ c).1<0) :
    (polynomialOfRow c).eval ((u₁ : ℝ)/v₁)*(polynomialOfRow c).eval ((u₂ : ℝ)/v₂)<0 := by
  have v₁R : (0 : ℝ)<v₁ := by exact_mod_cast v₁pos
  have v₂R : (0 : ℝ)<v₂ := by exact_mod_cast v₂pos
  have realSign : ((scaledValue u₁ v₁ c).1 : ℝ)*((scaledValue u₂ v₂ c).1 : ℝ)<0 := by exact_mod_cast opposite
  rw [scaledValue_correct _ _ v₁pos.ne',scaledValue_correct _ _ v₂pos.ne'] at realSign
  rw [mul_mul_mul_comm] at realSign
  exact neg_of_mul_neg_right realSign (mul_pos (pow_pos v₁R _) (pow_pos v₂R _)).le

end DukesRevstack
