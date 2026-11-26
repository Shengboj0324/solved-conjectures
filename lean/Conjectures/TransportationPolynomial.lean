import Conjectures.TransportationLaguerre

/-! The closed binomial numerator and the exact rational Laguerre certificate
for the full-support member with margins (1,1,12) and (2,1,...,1). -/

namespace TransportationEhrhart

open Polynomial

noncomputable def numerator (m : ℕ) : ℝ[X] :=
  (∑ j ∈ Finset.range (m+1), C ((m.choose j : ℝ)^2) * X^j) - C (m : ℝ) * X

theorem numerator_twelve : numerator 12 =
  1 + C 132 * X + C 4356 * X^2 + C 48400 * X^3 + C 245025 * X^4 + C 627264 * X^5 + C 853776 * X^6 + C 627264 * X^7 + C 245025 * X^8 + C 48400 * X^9 + C 4356 * X^10 + C 144 * X^11 + X^12 := by
  norm_num [numerator, Finset.sum_range_succ, Nat.choose, C_ofNat]
  ring

theorem certificate_values :
    5^12 * (numerator 12).eval (-1/5) = 41780056 ∧
    5^11 * (numerator 12).derivative.eval (-1/5) = -357481092 ∧
    5^10 * (numerator 12).derivative.derivative.eval (-1/5) = 12374409432 := by
  norm_num [numerator_twelve, map_add, derivative_C_mul_X_pow, derivative_C_mul_X,
    derivative_X_pow, derivative_C_mul, eval_add, eval_mul, eval_pow]

theorem certificate_negative :
    5^22 * laguerre (numerator 12) (-1/5) = -389210787898375728 := by
  obtain ⟨h,d,dd⟩ := certificate_values
  unfold laguerre
  norm_num at h d dd ⊢
  rw [show (numerator 12).eval (-(1/5)) = 41780056/244140625 by linarith,
      show (numerator 12).derivative.eval (-(1/5)) = -357481092/48828125 by linarith,
      show (numerator 12).derivative.derivative.eval (-(1/5)) = 12374409432/9765625 by linarith]
  norm_num

theorem twelve_not_real_rooted : ¬(numerator 12).Splits := by
  intro h
  have pos := splits_laguerre_nonneg h (-1/5)
  have neg := certificate_negative
  have : 0 ≤ (5:ℝ)^22 * laguerre (numerator 12) (-1/5) := mul_nonneg (by positivity) pos
  linarith only [this,neg]

end TransportationEhrhart
