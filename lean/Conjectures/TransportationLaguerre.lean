import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic

/-! The Laguerre inequality for every split real polynomial, including at its
roots. The product identity avoids any division by a polynomial value. -/

namespace TransportationEhrhart

open Polynomial

noncomputable def laguerre (p : ℝ[X]) (x : ℝ) : ℝ :=
  p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x

theorem laguerre_mul (p q : ℝ[X]) (x : ℝ) :
    laguerre (p*q) x = laguerre p x * q.eval x ^ 2 + p.eval x ^ 2 * laguerre q x := by
  simp only [laguerre, derivative_mul, map_add, eval_add, eval_mul]
  ring

theorem splits_laguerre_nonneg {p : ℝ[X]} (split : p.Splits) (x : ℝ) : 0 ≤ laguerre p x := by
  have mul_nonneg' {f g : ℝ[X]} (hf : 0 ≤ laguerre f x) (hg : 0 ≤ laguerre g x) :
      0 ≤ laguerre (f*g) x := by
    rw [laguerre_mul]
    exact add_nonneg (mul_nonneg hf (sq_nonneg _)) (mul_nonneg (sq_nonneg _) hg)
  have product (s : Multiset ℝ) : 0 ≤ laguerre (s.map (fun a => X-C a)).prod x := by
    induction s using Multiset.induction_on with
    | empty => simp [laguerre]
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact mul_nonneg' (by simp [laguerre]) ih
  obtain ⟨s,fac⟩ := splits_iff_exists_multiset.mp split
  exact fac ▸ mul_nonneg' (f := C p.leadingCoeff) (by simp [laguerre]) (product s)

end TransportationEhrhart
