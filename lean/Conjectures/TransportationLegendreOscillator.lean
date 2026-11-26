import Conjectures.TransportationLegendreEnergy
import Conjectures.TransportationSturmInterval

/-! Removal of the first-derivative term gives an oscillator with an explicit
potential. Sturm comparison then supplies a zero in each test interval. -/

namespace TransportationEhrhart

open Set

noncomputable def legendreOscillator (n : ℕ) (x : ℝ) :=
  Real.sqrt (legendreGap x)*(legendre n).eval x

noncomputable def oscillatorNumerator (n : ℕ) (x : ℝ) :=
  legendreGap x*(legendre n).derivative.eval x-x*(legendre n).eval x

noncomputable def oscillatorSlope (n : ℕ) (x : ℝ) :=
  oscillatorNumerator n x/Real.sqrt (legendreGap x)

noncomputable def legendrePotential (n : ℕ) (x : ℝ) :=
  legendreMass n/legendreGap x+1/legendreGap x^2

theorem sqrt_gap_deriv {x : ℝ} (h : 0<legendreGap x) :
    HasDerivAt (fun z => Real.sqrt (legendreGap z)) (-x/Real.sqrt (legendreGap x)) x := by
  apply ((legendre_gap_deriv x).sqrt h.ne').congr_deriv
  field_simp

theorem oscillator_deriv (n : ℕ) {x : ℝ} (h : 0<legendreGap x) :
    HasDerivAt (legendreOscillator n) (oscillatorSlope n x) x := by
  have nr := (Real.sqrt_pos.2 h).ne'
  apply ((sqrt_gap_deriv h).mul ((legendre n).hasDerivAt x)).congr_deriv
  unfold oscillatorSlope oscillatorNumerator
  rw [eq_div_iff nr]
  field_simp
  linear_combination (legendre n).derivative.eval x*(Real.sq_sqrt h.le)

theorem oscillator_numerator_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (oscillatorNumerator n)
      (-x*(legendre n).derivative.eval x-(legendreMass n+1)*(legendre n).eval x) x := by
  apply (((legendre_gap_deriv x).mul ((legendre n).derivative.hasDerivAt x)).sub
      ((hasDerivAt_id x).mul ((legendre n).hasDerivAt x))).congr_deriv
  dsimp
  linear_combination legendre_ode_eval n x

theorem oscillator_second_deriv (n : ℕ) {x : ℝ} (h : 0<legendreGap x) :
    HasDerivAt (oscillatorSlope n) (-legendrePotential n x*legendreOscillator n x) x := by
  let r:=Real.sqrt (legendreGap x)
  let s:=legendreGap x
  let c:=legendreMass n
  let y:=(legendre n).eval x
  let d:=(legendre n).derivative.eval x
  have nr : r≠0 := (Real.sqrt_pos.2 h).ne'
  have hr : r^2=s := Real.sq_sqrt h.le
  apply ((oscillator_numerator_deriv n x).div (sqrt_gap_deriv h) nr).congr_deriv
  change ((-x*d-(c+1)*y)*r-(s*d-x*y)*(-x/r))/r^2= -(c/s+1/s^2)*(r*y)
  calc
    _ = ((-x*d-(c+1)*y)*s+(s*d-x*y)*x)/(r*s) := by rw [←hr]; field_simp; ring
    _ = -(c*s+1)*y/(r*s) := by congr 1; dsimp [s,legendreGap]; ring
    _ = _ := by rw [←hr]; field_simp

theorem legendre_interval_zero (n : ℕ) {a b ω : ℝ}
    (ab : a<b) (pos : 0<ω) (period : ω*(b-a)=Real.pi)
    (gap : ∀ x∈Icc a b,0<legendreGap x)
    (high : ∀ x∈Ioo a b,ω^2<legendrePotential n x) :
    ∃ x∈Icc a b,(legendre n).eval x=0 := by
  obtain ⟨x,hx,h⟩ := oscillator_interval_zero ab pos period
    (fun x hx => oscillator_deriv n (gap x hx)) (fun x hx => oscillator_second_deriv n (gap x hx)) high
  exact ⟨x,hx,(mul_eq_zero.mp h).resolve_left (Real.sqrt_pos.2 (gap x hx)).ne'⟩

end TransportationEhrhart
