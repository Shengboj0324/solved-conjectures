import Conjectures.TransportationLegendreExpansion
import Conjectures.TransportationLegendreEnergy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exact coordinates and inequalities for the logarithmic interval. -/

namespace TransportationEhrhart

open Set Polynomial

noncomputable def windowScale (n : ℕ) : ℝ := Real.log n/(32*n)

theorem window_scale (n : ℕ) (hn : 0<(n : ℝ)) (hl : 32≤Real.log n) :
    0<windowScale n ∧ windowScale n≤1/32 ∧ 1≤(n : ℝ)*windowScale n := by
  unfold windowScale
  have pos : 0<32*(n : ℝ) := by positivity
  refine ⟨div_pos (by linarith) pos, (div_le_iff₀ pos).2 ?_,?_⟩
  · linarith [Real.log_le_self hn.le]
  · field_simp
    linarith

theorem coordinate_nonneg {z : ℝ} (hz : 0≤z) (h1 : z≤1) : 0≤legendreCoordinate z :=
  div_nonneg (sub_nonneg.mpr h1) (by linarith)

theorem coordinate_lt_one {z : ℝ} (hz : 0<z) : legendreCoordinate z<1 := by
  unfold legendreCoordinate
  apply (div_lt_iff₀ (by linarith)).2
  linarith

theorem coordinate_antitone {a b : ℝ} (a0 : 0≤a) (ab : a≤b) :
    legendreCoordinate b≤legendreCoordinate a := by
  unfold legendreCoordinate
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

theorem coordinate_involutive {z : ℝ} (hz : 0≤z) : legendreCoordinate (legendreCoordinate z)=z := by
  unfold legendreCoordinate
  have den : 1+z≠0 := by positivity
  have num : 1+(1-z)/(1+z)≠0 := by
    intro eq
    field_simp at eq
    linarith
  field_simp
  ring

theorem coordinate_gap {z : ℝ} (hz : 0≤z) :
    legendreGap (legendreCoordinate z)=4*z/(1+z)^2 := by
  unfold legendreGap legendreCoordinate
  have den : 1+z≠0 := by positivity
  field_simp
  ring

theorem coordinate_gap_bounds {z : ℝ} (hz : 0≤z) (h1 : z≤1) :
    z≤legendreGap (legendreCoordinate z) ∧ legendreGap (legendreCoordinate z)≤4*z := by
  rw [coordinate_gap hz]
  have d : 0<(1+z)^2 := by positivity
  have dlow : 1≤(1+z)^2 := by nlinarith [sq_nonneg z]
  have dhigh : (1+z)^2≤4 := by nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : 0≤3+z)]
  constructor
  · apply (le_div_iff₀ d).2
    nlinarith only [mul_le_mul_of_nonneg_left dhigh hz]
  · apply (div_le_iff₀ d).2
    nlinarith only [mul_le_mul_of_nonneg_left dlow hz]

theorem coordinate_window_width {t : ℝ} (ht : 0≤t) (small : 2*t≤1) :
    t/2≤legendreCoordinate t-legendreCoordinate (2*t) := by
  have den : 0<(1+t)*(1+2*t) := by positivity
  have cap : (1+t)*(1+2*t)≤4 := by
    calc
      (1+t)*(1+2*t) ≤ (2 : ℝ)*2 := mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
      _ = _ := by norm_num
  have eq : legendreCoordinate t-legendreCoordinate (2*t)=2*t/((1+t)*(1+2*t)) := by
    unfold legendreCoordinate
    field_simp
    ring
  rw [eq,le_div_iff₀ den]
  nlinarith only [mul_le_mul_of_nonneg_left cap ht]

theorem coordinate_window_inverse {t x : ℝ} (ht : 0<t) (small : 2*t≤1)
    (hx : x∈Icc (legendreCoordinate (2*t)) (legendreCoordinate t)) :
    0≤x ∧ x<1 ∧ legendreCoordinate x∈Icc t (2*t) := by
  have h0 := (coordinate_nonneg (by linarith : 0≤2*t) small).trans hx.1
  have hl := coordinate_antitone h0 hx.2
  have hu := coordinate_antitone (coordinate_nonneg (by linarith : 0≤2*t) small) hx.1
  rw [coordinate_involutive ht.le] at hl
  rw [coordinate_involutive (by linarith : 0≤2*t)] at hu
  exact ⟨h0,hx.2.trans_lt (coordinate_lt_one ht),hl,hu⟩

theorem binomialSquare_coeff (n j : ℕ) (hj : j≤n) :
    (binomialSquare n).coeff j=(n.choose j : ℝ)^2 := by
  classical
  simp only [binomialSquare,finsetSum_coeff,coeff_C_mul_X_pow]
  simp [Finset.mem_range.mpr (Nat.lt_succ_of_le hj)]

theorem binomialSquare_ne_zero (n : ℕ) : binomialSquare n≠0 := by
  intro h
  simpa [h] using binomialSquare_coeff n 0 (Nat.zero_le n)

theorem numerator_degree_lower (n : ℕ) (hn : 2≤n) : 2≤(numerator n).natDegree := by
  apply hn.trans
  apply Polynomial.le_natDegree_of_ne_zero
  rw [numerator_linear,Polynomial.coeff_sub,binomialSquare_coeff n n le_rfl,Polynomial.coeff_C_mul_X]
  simp [show n≠1 by omega]

end TransportationEhrhart
