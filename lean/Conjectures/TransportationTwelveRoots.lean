import Conjectures.TransportationPolynomial
import Conjectures.TransportationRootCount

/-! Ten disjoint rational sign intervals and the strict Laguerre obstruction
determine the exact number of real roots, with or without multiplicity. -/

namespace TransportationEhrhart

open Polynomial

noncomputable def cut : Fin 11 → ℝ := ![-1000,-107,-19,-7,-3,-2,-1,-1/2,-1/3,-1/29,0]

theorem cut_increasing : StrictMono cut := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i <;> norm_num [cut, Fin.succ, Fin.castSucc]

theorem cut_signs (i : Fin 10) :
    (numerator 12).eval (cut i.castSucc) * (numerator 12).eval (cut i.succ) < 0 := by
  fin_cases i <;> norm_num [cut, Fin.succ, Fin.castSucc, numerator_twelve,
    eval_add, eval_mul, eval_pow]

theorem twelve_degree : (numerator 12).natDegree=12 := by
  rw [numerator_twelve]
  compute_degree!

theorem twelve_real_roots : (numerator 12).roots.card=10 ∧ (numerator 12).roots.toFinset.card=10 := by
  classical
  have nonzero : numerator 12 ≠ 0 := fun h => by simpa [h] using twelve_degree
  have lower := count_sign_intervals nonzero cut cut_increasing cut_signs
  have upper := nonsplit_loses_two twelve_not_real_rooted
  have distinct := (numerator 12).roots.toFinset_card_le
  rw [twelve_degree] at upper
  omega

end TransportationEhrhart
