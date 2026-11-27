import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring

/-! Bases run through multiples of a fixed period. Rounding a slightly smaller
real radius preserves the target constant at every sufficiently large order. -/

open Filter

namespace NathansonSidon

noncomputable def radius (h N : ℕ) : ℝ := (N : ℝ)^((h : ℝ)⁻¹)

theorem radius_pow {h : ℕ} (hh : 0<h) (N : ℕ) : (radius h N)^h=N :=
  Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (Nat.ne_of_gt hh)

theorem radius_atTop {h : ℕ} (hh : 0<h) : Tendsto (radius h) atTop atTop :=
  (tendsto_rpow_atTop (inv_pos.mpr (by exact_mod_cast hh))).comp tendsto_natCast_atTop_atTop

theorem rounded_bases {h L u v : ℕ} (hh : 0<h) (hL : 0<L) (hu : 0<u) (hv : 0<v)
    (d : ℝ) (below : d<((v : ℝ)/u)^((h : ℝ)⁻¹)) :
    ∀ᶠ N : ℕ in atTop, ∃ r : ℕ, L∣r ∧ 0<r ∧ v≤u*r ∧ u*r^h≤v*(N-1) ∧
      d≤(r : ℝ)/radius h N := by
  let γ := ((v : ℝ)/u)^((h : ℝ)⁻¹)
  let k := max d 0
  let a := (k+γ)/2
  have uR : (0 : ℝ)<u := by exact_mod_cast hu
  have vR : (0 : ℝ)<v := by exact_mod_cast hv
  have LR : (0 : ℝ)<L := by exact_mod_cast hL
  have gp : 0<γ := Real.rpow_pos_of_pos (div_pos vR uR) _
  have kg : k<γ := max_lt below gp
  have kp : 0≤k := le_max_right _ _
  have ak : 0<a-k := by dsimp [a]; linarith
  have ap : 0<a := by linarith
  have ag : a<γ := by dsimp [a]; linarith
  have gh : γ^h=(v : ℝ)/u := Real.rpow_inv_natCast_pow (div_nonneg vR.le uR.le) (Nat.ne_of_gt hh)
  have aPow : a^h<(v : ℝ)/u := gh ▸ pow_lt_pow_left₀ ag ap.le (Nat.ne_of_gt hh)
  have room : 0<(v : ℝ)-u*a^h := by have := (lt_div_iff₀ uR).mp aPow; linarith
  have large₁ := (radius_atTop hh).eventually_ge_atTop (((L : ℝ)+v+1)/(a-k))
  have large₂ := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually_ge_atTop
    ((v : ℝ)/((v : ℝ)-u*a^h))
  filter_upwards [large₁,large₂,eventually_ge_atTop 1] with N n₁ n₂ npos
  have radpos : 0<radius h N := Real.rpow_pos_of_pos (by exact_mod_cast (show 0<N by omega)) _
  let base := ⌊(a*radius h N)/(L : ℝ)⌋₊
  let r := L*base
  have nonneg : 0≤(a*radius h N)/(L : ℝ) := (div_pos (mul_pos ap radpos) LR).le
  have floorLo := Nat.floor_le nonneg
  have floorHi := Nat.lt_floor_add_one ((a*radius h N)/(L : ℝ))
  have le : (r : ℝ) ≤ a*radius h N := by
    have h' := (le_div_iff₀ LR).mp floorLo
    change ((L*base : ℕ) : ℝ) ≤ _
    push_cast
    dsimp [base]; linarith
  have lt : a*radius h N-(L : ℝ)<r := by
    have h' := (div_lt_iff₀ LR).mp floorHi
    change _ < ((L*base : ℕ) : ℝ)
    push_cast
    dsimp [base]; linarith
  have cushion := (div_le_iff₀ ak).mp n₁
  have kprod := mul_nonneg kp radpos.le
  have rlarge : (v : ℝ)<r := by nlinarith only [lt,cushion,kprod]
  have natlarge : v<r := by exact_mod_cast rlarge
  have ur : r≤u*r := by simpa using Nat.mul_le_mul_right r (show 1≤u by omega)
  refine ⟨r,dvd_mul_right L base,by omega,by omega,?_,?_⟩
  · have raised := pow_le_pow_left₀ (show 0≤(r : ℝ) by positivity) le h
    rw [mul_pow,radius_pow hh] at raised
    have limit := mul_le_mul_of_nonneg_left raised uR.le
    have slack := (div_le_iff₀ room).mp n₂
    have cmp : (u : ℝ)*(r : ℝ)^h≤(v : ℝ)*((N : ℝ)-1) := by nlinarith only [limit,slack]
    rw [←Nat.cast_one (R := ℝ),←Nat.cast_sub npos] at cmp
    exact_mod_cast cmp
  · apply (le_div_iff₀ radpos).mpr
    have dk := mul_le_mul_of_nonneg_right (show d≤k from le_max_left _ _) radpos.le
    nlinarith only [lt,cushion,dk,vR]

end NathansonSidon
