import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! A one-interval Sturm comparison. A real solution of the oscillator
equation has a zero in every closed half-period of the slower sine wave. -/

namespace TransportationEhrhart

open Set

theorem oscillator_interval_zero {f d q : ℝ → ℝ} {a b ω : ℝ}
    (ab : a<b) (pos : 0<ω) (period : ω*(b-a)=Real.pi)
    (hf : ∀ x∈Icc a b,HasDerivAt f (d x) x)
    (hd : ∀ x∈Icc a b,HasDerivAt d (-q x*f x) x)
    (high : ∀ x∈Ioo a b,ω^2<q x) : ∃ x∈Icc a b,f x=0 := by
  by_contra! nz
  have ha := left_mem_Icc.mpr ab.le
  have hb := right_mem_Icc.mpr ab.le
  have cf : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have same (x : ℝ) (hx : x∈Icc a b) : 0<f x*f a := by
    by_contra! h
    have cont : ContinuousOn (fun t => f t*f a) (Icc a x) :=
      (cf.mono (Icc_subset_Icc_right hx.2)).mul continuousOn_const
    obtain ⟨t,ht,zero⟩ := intermediate_value_Icc' hx.1 cont
      (show 0∈Icc (f x*f a) (f a*f a) from ⟨h,mul_self_nonneg _⟩)
    exact (mul_ne_zero (nz t ⟨ht.1,ht.2.trans hx.2⟩) (nz a ha)) zero
  let w (x : ℝ) := (d x*Real.sin (ω*(x-a))-ω*f x*Real.cos (ω*(x-a)))*f a
  have dw (x : ℝ) (hx : x∈Icc a b) :
      HasDerivAt w ((ω^2-q x)*(f x*f a)*Real.sin (ω*(x-a))) x := by
    have phase : HasDerivAt (fun t => ω*(t-a)) ω x := by
      simpa using (((hasDerivAt_id x).sub_const a).const_mul ω)
    have raw := (((hd x hx).mul phase.sin).sub (((hf x hx).const_mul ω).mul phase.cos)).mul_const (f a)
    apply raw.congr_deriv
    ring
  have strict : StrictAntiOn w (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a b)
    · exact fun x hx => (dw x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(dw x ⟨hx.1.le,hx.2.le⟩).deriv]
      have hsin : 0<Real.sin (ω*(x-a)) := Real.sin_pos_of_pos_of_lt_pi
        (mul_pos pos (sub_pos.mpr hx.1)) (by rw [←period]; gcongr; exact hx.2)
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.mpr (high x hx))
        (same x ⟨hx.1.le,hx.2.le⟩)) hsin
  have contradict := strict ha hb ab
  simp only [w,sub_self,mul_zero,Real.sin_zero,Real.cos_zero,mul_one,
    period,Real.sin_pi,Real.cos_pi,mul_neg,sub_neg_eq_add,zero_add,zero_sub,neg_mul] at contradict
  have l := mul_pos pos (same a ha)
  have r := mul_pos pos (same b hb)
  linarith only [contradict,l,r]

end TransportationEhrhart
