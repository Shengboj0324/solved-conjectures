import Conjectures.NathansonSidonSharpProgression
import Conjectures.NathansonSidonLimit
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-! The progression construction applies at every sufficiently large ambient
order. Any two distinct coefficients contribute to the lower constant. -/

open Filter

namespace NathansonSidon

theorem coefficientGcd_reindex {h : ℕ} (c : Fin h → ℤ) (e : Equiv.Perm (Fin h)) :
    coefficientGcd (c ∘ e)=coefficientGcd c := by
  apply Nat.dvd_antisymm
  · apply Finset.dvd_gcd
    intro i _
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using gcd_dvd_weight (c ∘ e) (e.symm i)
  · exact Finset.dvd_gcd fun i _ => gcd_dvd_weight c (e i)

theorem pair_progression {h A B : ℕ} (hh : 0<h) (hA : 0<A) (hB : 0<B)
    (c : Fin h → ℤ) (nz : ∀ i,c i≠0) (a j : Fin h) (aj : a≠j)
    (slope : B*coefficientGcd c<A*((c a).natAbs+(c j).natAbs)) :
    ∃ C : ℕ, 0<C ∧ ∃ t₀ : ℕ, ∀ t≥t₀, ∀ N : ℕ, 0<N →
      A*(C*t)^h≤B*(N-1) → Feasible c N 1 (C*t) := by
  let k := lastIndex hh
  let e := Equiv.swap k j
  have ej : e k=j := Equiv.swap_apply_left _ _
  have neq : e.symm a≠k := fun eq => aj ((e.symm_apply_eq.mp eq).trans ej)
  have endp (i : Fin h) : i≤k := by change i.val≤h-1; omega
  obtain ⟨C,cp,t₀,sets⟩ := sharp_progression hh hA hB (c ∘ e) (fun i => nz (e i))
    (e.symm a) k neq endp (by simpa only [coefficientGcd_reindex,Function.comp_apply,Equiv.apply_symm_apply,ej] using slope)
  exact ⟨C,cp,t₀,fun t ht N hn budget => (feasible_reindex e c).mpr (sets t ht N hn budget)⟩

theorem pair_slope_eventually {h A B : ℕ} (hh : 0<h) (hA : 0<A) (hB : 0<B)
    (c : Fin h → ℤ) (nz : ∀ i,c i≠0) (a j : Fin h) (aj : a≠j)
    (slope : B*coefficientGcd c<A*((c a).natAbs+(c j).natAbs)) (d : ℝ)
    (hd : d<((B : ℝ)/A)^((h : ℝ)⁻¹)) :
    ∀ᶠ N : ℕ in atTop,d≤normalized c 1 N := by
  obtain ⟨C,cp,t₀,sets⟩ := pair_progression hh hA hB c nz a j aj slope
  have round := rounded_bases hh (Nat.mul_pos cp (Nat.succ_pos t₀)) hA hB d hd
  filter_upwards [round,eventually_ge_atTop 1] with N hn npos
  obtain ⟨q,⟨k,eq⟩,qpos,_,budget,bound⟩ := hn
  have kp : 0<k := Nat.pos_of_ne_zero (right_ne_zero_of_mul (eq ▸ qpos.ne'))
  have ht : t₀≤(t₀+1)*k := (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ kp)
  rw [Nat.mul_assoc] at eq
  have feasible := sets ((t₀+1)*k) ht N npos (eq ▸ budget)
  have card : q≤extremal c N 1 := eq ▸ feasible_le_extremal hh feasible
  apply bound.trans
  exact div_le_div_of_nonneg_right (by exact_mod_cast card) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

noncomputable def pairRatio {h : ℕ} (c : Fin h → ℤ) (a j : Fin h) : ℝ :=
  (((c a).natAbs+(c j).natAbs : ℕ) : ℝ)/(coefficientGcd c : ℝ)

theorem pairRatio_pos {h : ℕ} (hh : 0<h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0) (a j : Fin h) :
    0<pairRatio c a j := by
  unfold pairRatio
  exact div_pos (Nat.cast_pos.mpr (Nat.add_pos_left (Int.natAbs_pos.mpr (nz a)) _))
    (Nat.cast_pos.mpr (coefficientGcd_pos hh c nz))

theorem pair_eventually {h : ℕ} (hh : 0<h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0)
    (a j : Fin h) (aj : a≠j) (d : ℝ) (hd : d<(pairRatio c a j)^((h : ℝ)⁻¹)) :
    ∀ᶠ N : ℕ in atTop,d≤normalized c 1 N := by
  let k := max d 0
  have rp := pairRatio_pos hh c nz a j
  have kp : 0≤k := le_max_right _ _
  have kth : k<(pairRatio c a j)^((h : ℝ)⁻¹) := max_lt hd (Real.rpow_pos_of_pos rp _)
  have kt : k^h<pairRatio c a j := by
    have lp := pow_lt_pow_left₀ kth kp hh.ne'
    rwa [Real.rpow_inv_natCast_pow rp.le hh.ne'] at lp
  obtain ⟨q,hq,qu⟩ := exists_rat_btwn kt
  have qp : 0<q := Rat.cast_pos.mp ((pow_nonneg kp h).trans_lt hq)
  have numpos : 0<q.num.natAbs := Int.natAbs_pos.mpr (Rat.num_pos.mpr qp).ne'
  have repr : (q.num.natAbs : ℝ)/(q.den : ℝ)=(q : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    calc
      (q.num.natAbs : ℝ) = (((q.num.natAbs : ℕ) : ℤ) : ℝ) := by simp
      _ = _ := congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg (Rat.num_pos.mpr qp).le)
  have denom : (0 : ℝ)<q.den := Nat.cast_pos.mpr q.den_pos
  have gcdpos : (0 : ℝ)<coefficientGcd c := Nat.cast_pos.mpr (coefficientGcd_pos hh c nz)
  rw [←repr] at hq qu
  have cross := (div_lt_div_iff₀ denom gcdpos).mp qu
  have slope : q.num.natAbs*coefficientGcd c<q.den*((c a).natAbs+(c j).natAbs) := by
    rw [Nat.mul_comm q.den]
    exact_mod_cast cross
  have rootpos : 0≤((q.num.natAbs : ℝ)/q.den)^((h : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  have lower : k<((q.num.natAbs : ℝ)/q.den)^((h : ℝ)⁻¹) := by
    apply (pow_lt_pow_iff_left₀ kp rootpos hh.ne').mp
    rwa [Real.rpow_inv_natCast_pow (by positivity) hh.ne']
  exact pair_slope_eventually hh q.den_pos numpos c nz a j aj slope d ((le_max_left _ _).trans_lt lower)

theorem pair_liminf {h : ℕ} (hh : 0<h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0)
    (a j : Fin h) (aj : a≠j) : (pairRatio c a j)^((h : ℝ)⁻¹)≤liminf (normalized c 1) atTop := by
  by_contra! bad
  obtain ⟨d,above,below⟩ := exists_between bad
  exact above.not_ge (le_liminf_of_le (normalized_bounded hh c 1).isCoboundedUnder_ge
    (pair_eventually hh c nz a j aj d below))

end NathansonSidon
