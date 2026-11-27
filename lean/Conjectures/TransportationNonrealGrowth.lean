import Conjectures.TransportationWindowSuppression
import Conjectures.TransportationWindowOscillation
import Conjectures.TransportationComplexRoots

/-! An explicit square-root-logarithmic lower bound on nonreal roots,
with multiplicity, for the actual transportation numerators. -/

namespace TransportationEhrhart

open Polynomial Set Filter
open scoped Topology

theorem window_nonreal_loss (n N : ℕ) (hn : 16<(n : ℝ)) (hl : 32≤Real.log n)
    (count : (N : ℝ)*4*Real.pi≤windowFrequency n*windowScale n) :
    N≤(nonrealRoots (numerator n)).card+4 := by
  have hn0 : 0<(n : ℝ) := by linarith
  have t0:=(window_scale n hn0 hl).1
  have degree : 2≤n := by exact_mod_cast (show (2 : ℝ)≤n by linarith)
  have control := deficit_linear (p := numerator n) (f := binomialSquare n)
    (show -(2*windowScale n)≤ -windowScale n by linarith) (numerator_linear n)
    (fun x hx => by
      have pos := numerator_positive_on_window n (z := -x) hn hl
        (show -x∈Icc (windowScale n) (2*windowScale n) from ⟨by linarith [hx.2],by linarith [hx.1]⟩)
      simpa using pos.ne') (numerator_degree_lower n degree)
  have zeros:=window_distinct_roots n N hn0 hl count
  have full:=complex_root_accounting (numerator n)
  omega

theorem window_sqrt_frequency (n : ℕ) (hn : 0<(n : ℝ)) (hl : 32≤Real.log n) :
    Real.sqrt ((n : ℝ)*Real.log n)≤24*windowFrequency n*windowScale n := by
  let t:=windowScale n
  let r:=Real.sqrt t
  have t0 := (window_scale n hn hl).1
  have r0 : 0<r := Real.sqrt_pos.2 t0
  have hr : r^2=t := Real.sq_sqrt t0.le
  have scale : 32*(n : ℝ)*t=Real.log n := by dsimp [t,windowScale];field_simp
  have prod : windowFrequency n*t=(n : ℝ)*r/4 := by
    change (n : ℝ)/(4*r)*t=(n : ℝ)*r/4
    rw [←hr]
    field_simp
  have sq : (n : ℝ)*Real.log n≤(6*n*r)^2 := by
    rw [←scale,mul_pow,hr]
    have pos:=mul_nonneg (sq_nonneg (n : ℝ)) t0.le
    nlinarith only [pos]
  have cmp:=Real.sqrt_le_sqrt sq
  rw [Real.sqrt_sq (by positivity)] at cmp
  change _≤24*windowFrequency n*t
  linarith only [cmp,prod]

theorem explicit_nonreal_bound (n : ℕ) (hn : 16<(n : ℝ)) (hl : 32≤Real.log n) :
    Real.sqrt ((n : ℝ)*Real.log n)≤96*Real.pi*((nonrealRoots (numerator n)).card+5) := by
  have hn0 : 0<(n : ℝ) := by linarith
  have ht:=(window_scale n hn0 hl).1
  have hf : 0<windowFrequency n := div_pos hn0 (mul_pos (by norm_num) (Real.sqrt_pos.2 ht))
  let a:=windowFrequency n*windowScale n/(4*Real.pi)
  let N:=⌊a⌋₊
  have a0 : 0≤a := div_nonneg (mul_nonneg hf.le ht.le) (by positivity)
  have upper : (N : ℝ)*4*Real.pi≤windowFrequency n*windowScale n := by
    rw [mul_assoc]
    exact (le_div_iff₀ (by positivity)).mp (Nat.floor_le a0)
  have natloss := window_nonreal_loss n N hn hl upper
  have loss : (N : ℝ)≤(nonrealRoots (numerator n)).card+4 := by exact_mod_cast natloss
  have lower : a<(N : ℝ)+1 := Nat.lt_floor_add_one a
  have cap : a≤(nonrealRoots (numerator n)).card+5 := by linarith
  have prod := (div_le_iff₀ (by positivity : 0<4*Real.pi)).mp cap
  nlinarith only [window_sqrt_frequency n hn0 hl,prod]

theorem eventual_nonreal_growth : ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
    c*Real.sqrt ((n : ℝ)*Real.log n)≤((nonrealRoots (numerator n)).card : ℝ) := by
  refine ⟨1/(192*Real.pi),by positivity,?_⟩
  have natLimit : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have logLimit := Real.tendsto_log_atTop.comp natLimit
  filter_upwards [natLimit.eventually_ge_atTop 17,natLimit.eventually_ge_atTop ((960*Real.pi)^2),
    logLimit.eventually_ge_atTop 32] with n h17 hn hl
  change 32≤Real.log n at hl
  change (17 : ℝ)≤n at h17
  change (960*Real.pi)^2≤(n : ℝ) at hn
  have step : (n : ℝ)≤n*Real.log n := by
    have := mul_le_mul_of_nonneg_left (show 1≤Real.log n by linarith) (Nat.cast_nonneg (α := ℝ) n)
    simpa using this
  have large:=Real.sqrt_le_sqrt (hn.trans step)
  rw [Real.sqrt_sq (by positivity)] at large
  have h := explicit_nonreal_bound n (by linarith) hl
  rw [one_div,inv_mul_eq_div]
  apply (div_le_iff₀ (by positivity)).2
  nlinarith only [large,h]

end TransportationEhrhart
