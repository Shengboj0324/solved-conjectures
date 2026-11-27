import Conjectures.NathansonSidonSharpLimit
import Conjectures.NathansonSidonTheorems

/-! The two-largest-coefficient lower limit in every arity, and the exact
limit of the literal bilinear extremal function for all nonzero signed coefficients. -/

open Filter
open scoped Topology

namespace NathansonSidon

noncomputable def powerRatio {h : ℕ} (c : Fin h → ℤ) (N : ℕ) : ℝ :=
  (extremal c N 1 : ℝ)^h/(N : ℝ)

theorem normalized_pow {h : ℕ} (hh : 0<h) (c : Fin h → ℤ) (N : ℕ) :
    (normalized c 1 N)^h=powerRatio c N := by
  rw [normalized,powerRatio,div_pow,radius_pow hh]

theorem pair_power_eventually {h : ℕ} (hh : 0<h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0)
    (a j : Fin h) (aj : a≠j) (x : ℝ) (hx : x<pairRatio c a j) :
    ∀ᶠ N : ℕ in atTop,x<powerRatio c N := by
  have rp := pairRatio_pos hh c nz a j
  let u := (max x 0+pairRatio c a j)/2
  have below : max x 0<pairRatio c a j := max_lt hx rp
  have up : 0<u := by dsimp [u]; linarith [le_max_right x 0]
  have ux : x<u := by dsimp [u]; linarith [le_max_left x 0]
  have ur : u<pairRatio c a j := by dsimp [u]; linarith
  have lo := pair_eventually hh c nz a j aj (u^((h : ℝ)⁻¹))
    (Real.rpow_lt_rpow up.le ur (inv_pos.mpr (Nat.cast_pos.mpr hh)))
  filter_upwards [lo] with N lower
  have pw := pow_le_pow_left₀ (Real.rpow_nonneg up.le _) lower h
  rw [Real.rpow_inv_natCast_pow up.le hh.ne',normalized_pow hh] at pw
  exact ux.trans_le pw

theorem pair_power_liminf {h : ℕ} (hh : 0<h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0)
    (a j : Fin h) (aj : a≠j) : pairRatio c a j≤liminf (powerRatio c) atTop := by
  have bounded : IsBoundedUnder (· ≤ ·) atTop (powerRatio c) := by
    refine ⟨((coefficientSum c/coefficientGcd c : ℕ) : ℝ),?_⟩
    change ∀ᶠ N : ℕ in atTop,powerRatio c N≤_
    filter_upwards [eventually_ge_atTop 1] with N hn
    simpa only [powerRatio,Nat.cast_one,one_mul] using power_ratio_upper (g := 1) hh hn c nz
  by_contra! bad
  obtain ⟨x,above,below⟩ := exists_between bad
  exact above.not_ge (le_liminf_of_le bounded.isCoboundedUnder_ge
    ((pair_power_eventually hh c nz a j aj x below).mono fun _ v => v.le))

def distinctPairs (h : ℕ) : Finset (Fin h × Fin h) :=
  Finset.univ.filter fun p => p.1≠p.2

def topPairSum {h : ℕ} (c : Fin h → ℤ) : ℕ :=
  (distinctPairs h).sup fun p => (c p.1).natAbs+(c p.2).natAbs

theorem topPairSum_attained {h : ℕ} (hh : 2≤h) (c : Fin h → ℤ) :
    ∃ a j : Fin h,a≠j ∧ topPairSum c=(c a).natAbs+(c j).natAbs := by
  let a : Fin h := ⟨0,by omega⟩
  let j : Fin h := ⟨1,by omega⟩
  have neq : a≠j := by intro eq; have := congrArg Fin.val eq; simp [a,j] at this
  have ne : (distinctPairs h).Nonempty := ⟨(a,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,neq⟩⟩
  obtain ⟨p,mem,largest⟩ := Finset.exists_mem_eq_sup _ ne (fun p => (c p.1).natAbs+(c p.2).natAbs)
  exact ⟨p.1,p.2,(Finset.mem_filter.mp mem).2,largest⟩

theorem sum_pair_le_top {h : ℕ} (c : Fin h → ℤ) {a j : Fin h} (aj : a≠j) :
    (c a).natAbs+(c j).natAbs≤topPairSum c :=
  Finset.le_sup (s := distinctPairs h) (f := fun p => (c p.1).natAbs+(c p.2).natAbs)
    (b := (a,j)) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,aj⟩)

theorem two_largest_amount {h : ℕ} (hh : 2≤h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0) :
    (topPairSum c : ℝ)/(coefficientGcd c : ℝ)≤liminf (powerRatio c) atTop := by
  obtain ⟨a,j,aj,eq⟩ := topPairSum_attained hh c
  rw [eq]
  exact pair_power_liminf (by omega) c nz a j aj

theorem bilinear_gcd (c : Fin 2 → ℤ) :
    coefficientGcd c=(c 0).natAbs.gcd (c 1).natAbs := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (gcd_dvd_weight c 0) (gcd_dvd_weight c 1)
  · apply Finset.dvd_gcd
    intro i _
    fin_cases i
    · exact Nat.gcd_dvd_left _ _
    · exact Nat.gcd_dvd_right _ _

theorem bilinear_limit (c : Fin 2 → ℤ) (nz : ∀ i,c i≠0) :
    Tendsto (fun N : ℕ => (extremal c N 1 : ℝ)^2/(N : ℝ)) atTop
      (𝓝 ((((c 0).natAbs+(c 1).natAbs : ℕ) : ℝ)/((c 0).natAbs.gcd (c 1).natAbs : ℝ))) := by
  change Tendsto (powerRatio c) atTop _
  rw [←bilinear_gcd]
  change Tendsto (powerRatio c) atTop (𝓝 (pairRatio c 0 1))
  have dvd : coefficientGcd c∣coefficientSum c :=
    Finset.dvd_sum fun i _ => gcd_dvd_weight c i
  have cast : ((coefficientSum c/coefficientGcd c : ℕ) : ℝ)=pairRatio c 0 1 := by
    rw [Nat.cast_div dvd (Nat.cast_ne_zero.mpr (coefficientGcd_pos (by decide) c nz).ne')]
    rw [coefficientSum,Fin.sum_univ_two,pairRatio]
  apply tendsto_order.mpr
  refine ⟨fun x hx => pair_power_eventually (by decide) c nz 0 1 (by decide) x hx,?_⟩
  intro y hy
  filter_upwards [eventually_ge_atTop 1] with N hn
  have bound := power_ratio_upper (g := 1) (by decide) hn c nz
  simp only [Nat.cast_one,one_mul,cast] at bound
  exact bound.trans_lt hy

end NathansonSidon
