import Conjectures.KovalevRationalCertificate
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! The finite-dimensional fourth moment and the real inequalities used to
transfer the Gaussian estimates to Kovalev's counterfamily. -/

namespace KovalevHardySeparation

theorem pointwise_lower {u c x : ℝ} (hu : 0≤u) (hc : 0<c) (hx : 0<x) :
    min x 1 / Real.sqrt (u+c) ≤ x / Real.sqrt (u+c*x) := by
  have pos : 0<u+c := by positivity
  have posx : 0<u+c*x := by positivity
  apply (div_le_div_iff₀ (Real.sqrt_pos.2 pos) (Real.sqrt_pos.2 posx)).2
  by_cases h : x≤1
  · rw [min_eq_left h]
    apply mul_le_mul_of_nonneg_left _ hx.le
    apply Real.sqrt_le_sqrt
    nlinarith
  · have h1 : 1≤x := by linarith
    rw [min_eq_right h1,one_mul]
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt posx.le,Real.sq_sqrt pos.le]
    nlinarith only [mul_nonneg (sub_nonneg.mpr h1)
      (show 0≤(x+1)*u+c*x by positivity)]

theorem chi_square_threshold (k : ℕ) (hk : 500000≤k) :
    (999/1000 : ℝ) ≤ 1-1/Real.sqrt (2*k) := by
  have h : (500000 : ℝ)≤k := by exact_mod_cast hk
  have hs : (1000 : ℝ)≤Real.sqrt (2*k) :=
    Real.le_sqrt_of_sq_le (by linarith)
  have hp : 0<Real.sqrt (2*k) := by linarith
  have := (div_le_iff₀ hp).2 (show (1 : ℝ)≤1/1000*Real.sqrt (2*k) by linarith)
  linarith

noncomputable def gradient (k : ℕ) (u v : ℝ) : Fin (k+1) → ℝ :=
  Fin.cases u (fun _ => Real.sqrt ((1/40 : ℝ)/k)*v)

def fourthTrace {n : ℕ} (g : Fin n → ℝ) : ℝ :=
  (∑ i,g i^2)^2+2*∑ i,g i^4

noncomputable def fourthExpression (k : ℕ) (u v : ℝ) : ℝ :=
  (u^2+1/40*v^2)^2+2*u^4+2*(1/40)^2/(k : ℝ)*v^4

theorem gradient_fourth (k : ℕ) (hk : 0<k) (u v : ℝ) :
    fourthTrace (gradient k u v)=fourthExpression k u v := by
  have h : (0 : ℝ)<k := by exact_mod_cast hk
  have sq := Real.sq_sqrt (show 0≤(1/40 : ℝ)/k by positivity)
  have fourth : Real.sqrt ((1/40 : ℝ)/k)^4=((1/40 : ℝ)/k)^2 := by
    rw [show (4 : ℕ)=2*2 by decide,pow_mul,sq]
  simp only [fourthTrace,gradient,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_pow,sq,fourth,fourthExpression]
  field_simp [h.ne']
  ring

theorem strict_separation (k : ℕ) (u v : ℝ)
    (hu : 7767/10000≤u) (hv : (999/1000)*(2083/1000)≤v) :
    Real.pi^2/8 < fourthExpression k u v := by
  have piUpper : Real.pi<(355/113 : ℝ) :=
    Real.pi_lt_d20.trans (by norm_num)
  have hg : (355/113 : ℚ)^2/8<KovalevRationalCertificate.vLower :=
    sub_pos.mp KovalevRationalCertificate.gap_positive
  have gap : (355/113 : ℝ)^2/8<(KovalevRationalCertificate.vLower : ℝ) := by
    calc
      (355/113 : ℝ)^2/8 = (((355/113 : ℚ)^2/8 : ℚ) : ℝ) := by norm_num
      _ < _ := Rat.cast_lt.mpr hg
  have base : (KovalevRationalCertificate.vLower : ℝ) =
      ((7767/10000)^2+1/40*((999/1000)*(2083/1000))^2)^2+2*(7767/10000)^4 := by
    norm_num [KovalevRationalCertificate.vLower,KovalevRationalCertificate.a0,
      KovalevRationalCertificate.b0,KovalevRationalCertificate.factor,KovalevRationalCertificate.c]
  calc
    Real.pi^2/8 < (355/113 : ℝ)^2/8 := by gcongr
    _ < (KovalevRationalCertificate.vLower : ℝ) := gap
    _ ≤ (u^2+1/40*v^2)^2+2*u^4 := by rw [base]; gcongr
    _ ≤ fourthExpression k u v := le_add_of_nonneg_right (by positivity)

theorem gradient_separation (k : ℕ) (hk : 500000≤k) (a b u v : ℝ)
    (ha : 7767/10000≤a) (hb : 2083/1000≤b) (hu : a≤u)
    (hv : (1-1/Real.sqrt (2*k))*b≤v) :
    Real.pi^2/8 < fourthTrace (gradient k u v) := by
  rw [gradient_fourth k (by omega)]
  apply strict_separation _ _ _ (ha.trans hu)
  exact (mul_le_mul (chi_square_threshold k hk) hb (by norm_num)
    ((by norm_num : (0:ℝ)≤999/1000).trans (chi_square_threshold k hk))).trans hv

theorem normalized_fourth_moment {n : ℕ} (hn : 0<n) {m c h : ℝ} (hm : 0<m)
    (g : Fin n → ℝ) (hc : c^4=8*((n : ℝ)+2)*m^4/(Real.pi^2*n^3))
    (hh : h^4=fourthTrace g/(n*((n : ℝ)+2))) :
    (c*((n : ℝ)/m*h))^4=8*fourthTrace g/Real.pi^2 := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  rw [mul_pow,mul_pow,div_pow,hc,hh]
  field_simp [hm.ne',hnR.ne',Real.pi_ne_zero,(show (0 : ℝ)<n+2 by positivity).ne']

theorem lower_inequality_fails {scaled dual V : ℝ} (hpos : 0≤scaled)
    (hdual : dual=1) (hmoment : scaled^4=8*V/Real.pi^2) (hV : Real.pi^2/8<V) :
    dual<scaled := by
  rw [hdual]
  have large : 1<scaled^4 := by
    rw [hmoment]
    apply (lt_div_iff₀ (sq_pos_of_pos Real.pi_pos)).2
    linarith
  by_contra! h
  have upper : scaled^4 ≤ (1:ℝ)^4 := pow_le_pow_left₀ hpos h _
  norm_num at upper
  exact large.not_ge upper

end KovalevHardySeparation
