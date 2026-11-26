import Conjectures.TransportationLegendreCenter
import Conjectures.TransportationLegendreEnergy

/-! A uniform bound with endpoint dependence for the Legendre polynomials. -/

namespace TransportationEhrhart

theorem energy_zero (n : ℕ) : legendreEnergy n 0=(legendre n).eval 0^2+
    (2*(legendre n).derivative.eval 0)^2/(legendreWeight n+1) := by
  simp [legendreEnergy,legendreMomentum,legendreGap,legendreDen]

theorem energy_center_bound (n : ℕ) : legendreEnergy n 0≤2/((n : ℝ)+1) := by
  obtain ⟨k,h | h⟩ := Nat.even_or_odd' n
  · subst n
    obtain ⟨v,d⟩ := even_center k
    rw [energy_zero,v,d]
    have eq : ((-1 : ℝ)^k*centralAmplitude k)^2=(centralAmplitude k)^2 := by
      rcases neg_one_pow_eq_or ℝ k with s | s <;> simp [s]
    simp only [eq,mul_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_div,add_zero]
    apply (le_div_iff₀ (by positivity)).2
    push_cast
    nlinarith only [central_square_bound k,sq_nonneg (centralAmplitude k)]
  · subst n
    obtain ⟨v,d⟩ := odd_center k
    have eq : (2*((-1 : ℝ)^k*((2*k+1 : ℕ) : ℝ)*centralAmplitude k))^2=
        (2*(2*(k : ℝ)+1))^2*(centralAmplitude k)^2 := by
      rcases neg_one_pow_eq_or ℝ k with s | s <;> rw [s] <;> push_cast <;> ring
    rw [energy_zero,v,d,eq]
    simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_add]
    have wn : 0<legendreWeight (2*k+1)+1 := by unfold legendreWeight legendreMass; positivity
    have co : (2*(2*(k : ℝ)+1))^2≤legendreWeight (2*k+1)+1 := by
      unfold legendreWeight legendreMass
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    calc
      _ ≤ (centralAmplitude k)^2 := (div_le_iff₀ wn).2 (by
        rw [mul_comm ((centralAmplitude k)^2)]
        exact mul_le_mul_of_nonneg_right co (sq_nonneg _))
      _ ≤ _ := by
        apply (le_div_iff₀ (by positivity)).2
        push_cast
        linarith [central_square_bound k]

theorem legendre_uniform_bound (n : ℕ) {x : ℝ} (hx : 0≤x) (h1 : x<1) :
    Real.sqrt (legendreGap x)*(legendre n).eval x^2≤2/((n : ℝ)+1) := by
  have s : 0≤legendreGap x := by
    unfold legendreGap
    nlinarith [mul_nonneg (sub_nonneg.mpr h1.le) (by linarith : 0≤1+x)]
  have wt := legendre_den_pos n s
  calc
    _ ≤ legendreEnergy n x := by
      unfold legendreEnergy
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) wt.le)
    _ ≤ legendreEnergy n 0 := legendre_energy_le_center n hx h1
    _ ≤ _ := energy_center_bound n

end TransportationEhrhart
