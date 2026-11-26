import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Integer elimination in the two-set inequality, preserving the constant 17. -/

namespace ErdosGyarfasSpectrum

theorem half_bound {t M A S C : ℤ} (ht : 2≤t) (hm : 0≤M) (hs : 0≤S)
    (hS : S≤t*M) (hA : 2*A≤t*(t+1)+2*t*M) (hC : t^2-A≤C)
    (hcauchy : C^2≤(t*(t-1)+S)*S) : t≤8*M+1 := by
  by_contra! bad
  have hm' : 0≤t*M := mul_nonneg (by omega) hm
  have left := mul_nonneg (show 0≤t by omega) (show 0≤t-1-2*M by omega)
  have lower : t*(t-1-2*M) ≤ 2*C := by nlinarith
  have sqLower := mul_self_le_mul_self left lower
  have room : 0≤t*(t-1)+t*M := add_nonneg (mul_nonneg (by omega) (by omega)) hm'
  have sqUpper := hcauchy.trans (mul_le_mul (show t*(t-1)+S ≤ t*(t-1)+t*M by omega) hS hs room)
  have positive : 0<t^2*(t-1)*(t-1-8*M) :=
    mul_pos (mul_pos (sq_pos_of_pos (by omega)) (by omega)) (by omega)
  nlinarith only [sqLower,sqUpper,positive]

end ErdosGyarfasSpectrum
