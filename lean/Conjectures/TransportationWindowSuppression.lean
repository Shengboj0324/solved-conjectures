import Conjectures.TransportationLogWindow
import Conjectures.TransportationLegendreBound

/-! The linear perturbation clears the entire logarithmic interval. -/

namespace TransportationEhrhart

open Polynomial Set

theorem window_power_bound (n : ℕ) {z : ℝ} (hn : 0<(n : ℝ))
    (hz : 0≤z) (upper : z≤2*windowScale n) :
    ((1+z)^n)^8≤(n : ℝ) := by
  have scale : 32*(n : ℝ)*windowScale n=Real.log n := by
    unfold windowScale
    field_simp
  have hlog : 8*(n : ℝ)*z≤Real.log n := by
    have bound := mul_le_mul_of_nonneg_left upper (by positivity : 0≤(n : ℝ))
    nlinarith only [scale,bound,mul_nonneg hn.le hz]
  calc
    _ = (1+z)^(8*n) := by rw [←pow_mul,Nat.mul_comm]
    _ ≤ (Real.exp z)^(8*n) := pow_le_pow_left₀ (by linarith)
      (by simpa [add_comm] using Real.add_one_le_exp z) _
    _ = Real.exp (((8*n : ℕ) : ℝ)*z) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr (by push_cast; exact hlog)
    _ = _ := Real.exp_log hn

theorem window_binomial_small (n : ℕ) {z : ℝ} (hn : 16<(n : ℝ)) (hl : 32≤Real.log n)
    (hz : z∈Icc (windowScale n) (2*windowScale n)) :
    |(binomialSquare n).eval (-z)|<1 := by
  have hn0 : 0<(n : ℝ) := by linarith
  obtain ⟨t0,th,tm⟩ := window_scale n hn0 hl
  have z0 := t0.trans_le hz.1
  have z1 : z≤1 := by linarith [hz.2]
  let x:=legendreCoordinate z
  let s:=legendreGap x
  let r:=Real.sqrt s
  let y:=(legendre n).eval x
  let k:=(1+z)^n
  let A:=((n : ℝ)+1)^2*s
  have s0 : 0<s := z0.trans_le (coordinate_gap_bounds z0.le z1).1
  have hr : r^2=s := Real.sq_sqrt s0.le
  have kr : 0≤k := by dsimp [k]; positivity
  have q : (k^4)^2≤(n : ℝ) := by
    rw [←pow_mul]
    exact window_power_bound n hn0 z0.le hz.2
  have ksmall : 4*k^4<(n : ℝ) := by nlinarith only [q,hn,sq_nonneg (k^4-4)]
  have ns : 1≤(n : ℝ)*s := tm.trans (mul_le_mul_of_nonneg_left
    (hz.1.trans (coordinate_gap_bounds z0.le z1).1) hn0.le)
  have Ahi : (n : ℝ)≤A := by
    have step := mul_le_mul_of_nonneg_left ns hn0.le
    have scale := mul_le_mul_of_nonneg_right (show (n : ℝ)^2≤((n : ℝ)+1)^2 by nlinarith) s0.le
    dsimp [A]
    nlinarith only [step,scale]
  have kernel : r*y^2≤2/((n : ℝ)+1) :=
    legendre_uniform_bound n (coordinate_nonneg z0.le z1) (coordinate_lt_one z0)
  have basic : (r*y^2)*((n : ℝ)+1)≤2 := (le_div_iff₀ (by positivity)).1 kernel
  have square : A*y^4≤4 := by
    calc
      _ = ((r*y^2)*((n : ℝ)+1))^2 := by dsimp [A]; rw [←hr]; ring
      _ ≤ (2 : ℝ)^2 := pow_le_pow_left₀ (by dsimp [r]; positivity) basic _
      _ = _ := by norm_num
  rw [binomialSquare_transform n z0.le]
  change |k*y|<1
  by_contra! large
  have pow4 : 1≤(k*y)^4 := by
    have hpow := pow_le_pow_left₀ (by norm_num : 0≤(1 : ℝ)) large 4
    rwa [one_pow,←abs_pow,abs_of_nonneg (by positivity : 0≤(k*y)^4)] at hpow
  have cap : A≤4*k^4 := calc
    A ≤ A*(k*y)^4 := by simpa using mul_le_mul_of_nonneg_left pow4 (hn0.le.trans Ahi)
    _ = k^4*(A*y^4) := by ring
    _ ≤ k^4*4 := mul_le_mul_of_nonneg_left square (by positivity)
    _ = _ := by ring
  linarith

theorem numerator_positive_on_window (n : ℕ) {z : ℝ} (hn : 16<(n : ℝ)) (hl : 32≤Real.log n)
    (hz : z∈Icc (windowScale n) (2*windowScale n)) : 0<(numerator n).eval (-z) := by
  have h := (abs_lt.mp (window_binomial_small n hn hl hz)).1
  have scale := (window_scale n (by linarith) hl).2.2
  have lower := mul_le_mul_of_nonneg_left hz.1 (by positivity : 0≤(n : ℝ))
  rw [numerator_linear,eval_sub,eval_mul,eval_C,eval_X]
  linarith

end TransportationEhrhart
