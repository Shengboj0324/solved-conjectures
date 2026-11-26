import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Conjectures.LonelinessRational
import Conjectures.LonelinessPairBridge
import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace ZhangDeletion

/-- In the boundary case, the first admissible denominator is already coprime. -/
theorem boundary_coprime (r : ℕ) : Nat.Coprime (3 * r + 1) r := by
  simp [Nat.add_comm]

theorem coprime_in_window (n r : ℕ) (hn : 1 ≤ n) (hr : 0 < r) :
    ∃ d, n + r ≤ d ∧ d ≤ n + 2*r - 1 ∧ Nat.Coprime d r := by
  let q := (n + r - 2) / r
  let d := 1 + (q + 1)*r
  have hm := Nat.mod_lt (n+r-2) hr
  have he := Nat.mod_add_div (n+r-2) r
  refine ⟨d, ?_, ?_, ?_⟩
  · dsimp [d, q]; simp only [Nat.mul_comm, Nat.mul_add, Nat.mul_one] at *; omega
  · dsimp [d, q]; simp only [Nat.mul_comm, Nat.mul_add, Nat.mul_one] at *; omega
  · dsimp [d]; exact (Nat.coprime_add_mul_right_left 1 r (q+1)).2 (Nat.coprime_one_left r)

theorem coprime_strict_window (n r : ℕ) (hn : 4 ≤ n) (hr : 1 ≤ r)
    (hsmall : 2*r ≤ n-1) :
    ∃ d, n+r ≤ d ∧ d ≤ 2*n-3 ∧ Nat.Coprime d r := by
  by_cases h : 2*r ≤ n-2
  · obtain ⟨d, hlow, hupp, hc⟩ := coprime_in_window n r (by omega) (by omega)
    exact ⟨d, hlow, by omega, hc⟩
  · refine ⟨3*r+1, ?_, ?_, boundary_coprime r⟩ <;> omega

theorem residue_ne_one (D j r v : ℕ) (hj : Nat.Coprime D j)
    (hrD : r < D) (hvD : v < D) (hvr : v ≠ r)
    (hjr : (r*j) % D = 1) : (v*j) % D ≠ 1 := by
  intro h
  have heq : v*j ≡ r*j [MOD D] := by
    change (v*j) % D = (r*j) % D
    omega
  have hcancel := Nat.ModEq.cancel_right_of_coprime hj heq
  change v % D = r % D at hcancel
  simp only [Nat.mod_eq_of_lt hvD, Nat.mod_eq_of_lt hrD] at hcancel
  exact hvr hcancel

theorem residue_ne_zero (D j v : ℕ) (hj : Nat.Coprime D j)
    (hvD : v < D) (hv : 0 < v) : (v*j) % D ≠ 0 := by
  intro h
  have heq : v*j ≡ 0*j [MOD D] := by
    change (v*j) % D = (0*j) % D
    simp [h]
  have hcancel := Nat.ModEq.cancel_right_of_coprime hj heq
  change v % D = 0 % D at hcancel
  simp only [Nat.mod_eq_of_lt hvD, Nat.zero_mod] at hcancel
  omega

theorem residue_ne_last (D j r v : ℕ) (hj : Nat.Coprime D j)
    (hD : 1 < D) (hvrD : v+r < D) (hv : 0 < v)
    (hjr : (r*j) % D = 1) : (v*j) % D ≠ D-1 := by
  intro h
  have heq : (v+r)*j ≡ 0*j [MOD D] := by
    change ((v+r)*j) % D = (0*j) % D
    rw [Nat.add_mul, Nat.add_mod, h, hjr]
    simp only [Nat.zero_mul, Nat.zero_mod]
    have : D-1+1 = D := by omega
    rw [this, Nat.mod_self]
  have hcancel := Nat.ModEq.cancel_right_of_coprime hj heq
  change (v+r) % D = 0 % D at hcancel
  simp only [Nat.mod_eq_of_lt hvrD, Nat.zero_mod] at hcancel
  omega

theorem inverse_witness (D r : ℕ) (hD : 1 < D) (hr : Nat.Coprime r D) :
    ∃ j, j < D ∧ Nat.Coprime D j ∧ (r*j) % D = 1 := by
  let : NeZero D := ⟨by omega⟩
  let j := ((r : ZMod D)⁻¹).val
  refine ⟨j, ZMod.val_lt _, ?_, ?_⟩
  · have he := ZMod.mul_val_inv hr
    have hu : IsUnit ((r : ZMod D) * (j : ZMod D)) := by
      rw [show (r : ZMod D) * (j : ZMod D) = 1 from he]
      exact isUnit_one
    exact ((ZMod.isUnit_iff_coprime j D).1 (isUnit_of_mul_isUnit_right hu)).symm
  · have he := ZMod.mul_val_inv hr
    have he' : ((r*j : ℕ) : ZMod D) = ((1 : ℕ) : ZMod D) := by
      simpa only [Nat.cast_mul, Nat.cast_one] using he
    have hm := (ZMod.natCast_eq_natCast_iff' (r*j) 1 D).1 he'
    simpa [Nat.mod_eq_of_lt hD] using hm

theorem modular_witness (n r D : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hD : n+r ≤ D) (hc : Nat.Coprime r D) :
    ∃ j, j < D ∧ ∀ v, 1 ≤ v → v < n → v ≠ r →
      2 ≤ (v*j) % D ∧ (v*j) % D ≤ D-2 := by
  have hD1 : 1 < D := by omega
  obtain ⟨j, hjD, hj, hjr⟩ := inverse_witness D r hD1 hc
  refine ⟨j, hjD, ?_⟩
  intro v hv hvn hvr
  have h0 := residue_ne_zero D j v hj (by omega) (by omega)
  have h1 := residue_ne_one D j r v hj (by omega) (by omega) hvr hjr
  have hl := residue_ne_last D j r v hj hD1 (by omega) (by omega) hjr
  have hm := Nat.mod_lt (v*j) (by omega : 0 < D)
  omega

theorem distance_bound (D v j a : ℕ) (hD : 0 < D)
    (hlo : a ≤ (v*j)%D) (hhi : (v*j)%D + a ≤ D) :
    (a : ℝ) / D ≤ Loneliness.distance (((v*j : ℕ) : ℝ) / D) := by
  have hDi : (0 : ℤ) < D := by exact_mod_cast hD
  have hd := Loneliness.distance_int_div (v*j : ℕ) D hDi
  simp only [Int.cast_natCast] at hd
  rw [hd]
  have hm : (a : ℤ) ≤ min (((v*j : ℕ) : ℤ) % D) (D - (((v*j : ℕ) : ℤ) % D)) := by
    apply le_min
    · rw [← Int.natCast_emod]
      exact_mod_cast hlo
    · rw [← Int.natCast_emod]
      have h1 : (a : ℤ) ≤ (D : ℤ) - (((v*j)%D : ℕ) : ℤ) := by
        have hh : (a : ℤ) + (((v*j)%D : ℕ) : ℤ) ≤ D := by
          have : a + (v*j)%D ≤ D := by omega
          exact_mod_cast this
        omega
      exact h1
  have hmR : (a : ℝ) ≤ ((min (((v*j : ℕ) : ℤ) % D) (D - (((v*j : ℕ) : ℤ) % D)) : ℤ) : ℝ) := by exact_mod_cast hm
  exact div_le_div_of_nonneg_right hmR (by positivity)

def speeds (n r : ℕ) : List ℕ := (List.range' 1 (n-1)).filter (· != r)

theorem modular_lower (n r D : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r)
    (hD : n+r ≤ D) (hc : Nat.Coprime r D) :
    (2 : ℝ) / D ≤ Loneliness.value (speeds n r) := by
  obtain ⟨j, hjD, hj⟩ := modular_witness n r D (by omega) hr hD hc
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hD4 : (4 : ℝ) ≤ D := by exact_mod_cast (show 4 ≤ D by omega)
  apply le_trans ?_ (Loneliness.le_value (ds := speeds n r) (t := (j : ℝ)/D) ?_)
  · apply Loneliness.le_clearance
    · apply (div_le_iff₀ hDR).2
      linarith
    · intro v hv
      have hv' : v ∈ List.range' 1 (n-1) ∧ v ≠ r := by
        simpa [speeds] using hv
      have hvBounds : 1 ≤ v ∧ v < n := by
        have h := hv'.1
        simp only [List.mem_range', Nat.one_mul] at h
        obtain ⟨i, hi, rfl⟩ := h
        omega
      obtain ⟨hlo, hhi⟩ := hj v hvBounds.1 hvBounds.2 hv'.2
      have hb := distance_bound D v j 2 (by omega) hlo (by omega)
      push_cast at hb
      simpa only [mul_div_assoc] using hb
  · constructor
    · positivity
    · apply (div_le_one hDR).2
      exact_mod_cast (Nat.le_of_lt hjD)

theorem small_deletion_strict (n r : ℕ) (hn : 4 ≤ n) (hr : 1 ≤ r)
    (hsmall : 2*r ≤ n-1) :
    (1 : ℝ) / (n-1) < Loneliness.value (speeds n r) := by
  obtain ⟨D, hD, hDmax, hc⟩ := coprime_strict_window n r hn hr hsmall
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hDr : (D : ℝ) + 3 ≤ 2*(n : ℝ) := by
    have h : D + 3 ≤ 2*n := by omega
    exact_mod_cast h
  have hstrict : (1 : ℝ) / (n-1) < 2 / D := by
    apply (div_lt_div_iff₀ (by linarith) hDR).2
    linarith
  exact hstrict.trans_le (modular_lower n r D (by omega) hr hD hc.symm)

theorem large_deletion_lower (n r : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n-1) (hlarge : n-1 < 2*r) :
    (1 : ℝ) / r ≤ Loneliness.value (speeds n r) := by
  have hr2 : 2 ≤ r := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hr2R : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  apply le_trans ?_ (Loneliness.le_value (ds := speeds n r) (t := (1 : ℝ)/r) ?_)
  · apply Loneliness.le_clearance
    · apply (div_le_iff₀ hrR).2
      linarith
    · intro v hv
      have hv' : v ∈ List.range' 1 (n-1) ∧ v ≠ r := by simpa [speeds] using hv
      have hvBounds : 1 ≤ v ∧ v < n := by
        have h := hv'.1
        simp only [List.mem_range', Nat.one_mul] at h
        obtain ⟨i, hi, rfl⟩ := h
        omega
      have hmod : 1 ≤ v%r ∧ v%r+1 ≤ r := by
        by_cases h : v < r
        · rw [Nat.mod_eq_of_lt h]; omega
        · have hvr : r ≤ v := by omega
          have hv2 : v-r < r := by omega
          have hvEq : v = r + (v-r) := by omega
          have hvmod : v % r = v-r := by
            conv_lhs => rw [hvEq]
            simp [Nat.mod_eq_of_lt hv2]
          rw [hvmod]
          omega
      have hb := distance_bound r v 1 1 (by omega) (by simpa using hmod.1) (by simpa using hmod.2)
      simpa [div_eq_mul_inv] using hb
  · constructor
    · positivity
    · apply (div_le_one hrR).2
      linarith

theorem question84 (n r : ℕ) (hn : 4 ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n-2) :
    (1 : ℝ) / (n-1) < Loneliness.value (speeds n r) := by
  by_cases hs : 2*r ≤ n-1
  · exact small_deletion_strict n r hn hr hs
  · have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hnR : (0 : ℝ) < (n : ℝ)-1 := by
      have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      linarith
    have hlt : (1 : ℝ) / (n-1) < 1/r := by
      apply (div_lt_div_iff₀ hnR hrR).2
      have h : (r : ℝ) + 2 ≤ n := by
        have hnat : r+2 ≤ n := by omega
        exact_mod_cast hnat
      linarith
    exact hlt.trans_le (large_deletion_lower n r (by omega) hr (by omega) (by omega))

theorem large_deletion_upper (n r : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n-1) (hlarge : n-1 < 2*r) :
    Loneliness.value (speeds n r) ≤ (1 : ℝ) / r := by
  have hr2 : 2 ≤ r := by omega
  apply Loneliness.value_le
  intro t ht
  obtain ⟨d, hd, hdn, hdist⟩ := Real.exists_nat_abs_mul_sub_round_le t (show 0 < r-1 by omega)
  have hmem : d ∈ speeds n r := by
    simp only [speeds, List.mem_filter, List.mem_range', bne_iff_ne, Nat.one_mul]
    constructor
    · exact ⟨d-1, by omega, by omega⟩
    · omega
  have hbound := Loneliness.clearance_le_of_mem hmem t
  have hEq : ((r-1 : ℕ) : ℝ)+1 = r := by
    have hh : r-1+1 = r := by omega
    exact_mod_cast hh
  rw [hEq] at hdist
  exact hbound.trans hdist

theorem large_deletion_exact (n r : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n-1) (hlarge : n-1 < 2*r) :
    Loneliness.value (speeds n r) = (1 : ℝ) / r :=
  le_antisymm (large_deletion_upper n r hn hr hrn hlarge)
    (large_deletion_lower n r hn hr hrn hlarge)

noncomputable def leastDenominator (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) : ℕ :=
  Nat.find (coprime_in_window n r hn hr)

theorem leastDenominator_spec (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    n+r ≤ leastDenominator n r hn hr ∧
      Nat.Coprime (leastDenominator n r hn hr) r := by
  have h := Nat.find_spec (coprime_in_window n r hn hr)
  exact ⟨h.1, h.2.2⟩

theorem leastDenominator_minimal (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (d : ℕ) (hd : n+r ≤ d) (hc : Nat.Coprime d r) :
    leastDenominator n r hn hr ≤ d := by
  by_cases h : d ≤ n+2*r-1
  · exact Nat.find_min' (coprime_in_window n r hn hr) ⟨hd, h, hc⟩
  · have hspec := Nat.find_spec (coprime_in_window n r hn hr)
    change Nat.find (coprime_in_window n r hn hr) ≤ d
    omega

theorem small_deletion_lower (n r : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r) :
    (2 : ℝ) / leastDenominator n r (by omega) hr ≤ Loneliness.value (speeds n r) := by
  have h := leastDenominator_spec n r (by omega) hr
  exact modular_lower n r _ hn hr h.1 h.2.symm

theorem opposite_residue (p r j : ℕ) (hp : 1 < p) (hr : r < p)
    (h : (r*j)%p = 1) : ((p-r)*j)%p = p-1 := by
  have he : (p-r)*j + r*j = p*j := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hm := congrArg (fun x : ℕ => x % p) he
  rw [Nat.add_mod, h] at hm
  simp only [Nat.mul_mod_right] at hm
  have hlt := Nat.mod_lt ((p-r)*j) (by omega : 0 < p)
  have hlt2 : ((p-r)*j)%p + 1 ≤ p := by omega
  by_cases heq : ((p-r)*j)%p + 1 < p
  · rw [Nat.mod_eq_of_lt heq] at hm
    omega
  · omega

theorem denominator_bound (n r p j : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r)
    (hsmall : 2*r ≤ n-1) (hp : n-1 < p)
    (hunit : (r*j)%p = 1)
    (hretained : ∀ v, 1 ≤ v → v < n → v ≠ r →
      2 ≤ (v*j)%p ∧ (v*j)%p + 2 ≤ p) : n+r ≤ p := by
  have hrl : r < p := by omega
  have hp1 : 1 < p := (lt_of_lt_of_le (by decide : 1 < 3) hn).trans_le (by omega)
  have hlast := opposite_residue p r j hp1 hrl hunit
  by_contra h
  have hpr : 1 ≤ p-r := by omega
  have hprn : p-r < n := by omega
  have hne : p-r ≠ r := by omega
  have hh := hretained (p-r) hpr hprn hne
  omega

theorem double_residue (p r j : ℕ) (hp : 2 < p)
    (h : (r*j)%p = 1) : ((2*r)*j)%p = 2 := by
  have he : (2*r)*j = r*j + r*j := by simp [Nat.two_mul, Nat.add_mul]
  rw [he, Nat.add_mod, h]
  norm_num [Nat.mod_eq_of_lt hp]

theorem retained_double_bound (n r p j : ℕ) (hr : 1 ≤ r)
    (hsmall : 2*r ≤ n-1) (hp : 2 < p) (h : (r*j)%p = 1)
    (q : ℕ) (hq : ∀ v, 1 ≤ v → v < n → v ≠ r → q ≤ (v*j)%p) : q ≤ 2 := by
  have hv := hq (2*r) (by omega) (by omega) (by omega)
  rw [double_residue p r j hp h] at hv
  exact hv

theorem positive_residues_denominator (n r p j : ℕ) (hr : 1 ≤ r)
    (hsmall : 2*r ≤ n-1) (hp : 1 ≤ p)
    (hpositive : ∀ v, 1 ≤ v → v < n → v ≠ r → 1 ≤ (v*j)%p) : n ≤ p := by
  by_contra h
  have hpn : p < n := by omega
  by_cases heq : p = r
  · have hv := hpositive (2*r) (by omega) (by omega) (by omega)
    subst p
    have hz : ((2*r)*j)%r = 0 := by
      rw [Nat.mul_assoc, Nat.mul_comm r j, ← Nat.mul_assoc]
      simp
    omega
  · have hv := hpositive p hp hpn heq
    simp at hv

theorem opposite_last_to_one (p r j : ℕ) (hp : 2 < p) (hr : r < p)
    (h : (r*j)%p = p-1) : ((p-r)*j)%p = 1 := by
  have he : (p-r)*j + r*j = p*j := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hm := congrArg (fun x : ℕ => x % p) he
  rw [Nat.add_mod, h] at hm
  simp only [Nat.mul_mod_right] at hm
  have hlt := Nat.mod_lt ((p-r)*j) (by omega : 0 < p)
  have hsum : ((p-r)*j)%p + (p-1) < 2*p := by omega
  by_cases hsmall : ((p-r)*j)%p + (p-1) < p
  · rw [Nat.mod_eq_of_lt hsmall] at hm
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : p ≤ ((p-r)*j)%p + (p-1))] at hm
    rw [Nat.mod_eq_of_lt (by omega : ((p-r)*j)%p + (p-1)-p < p)] at hm
    omega

theorem inverse_is_removed (n r p j : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r)
    (hsmall : 2*r ≤ n-1) (hp : n ≤ p) (hpmax : p ≤ 2*(n-1))
    (hj : Nat.Coprime p j)
    (hretained : ∀ v, 1 ≤ v → v < n → v ≠ r →
      2 ≤ (v*j)%p ∧ (v*j)%p + 2 ≤ p) :
    (r*j)%p = 1 ∨ (r*j)%p = p-1 := by
  have two_le : 2 ≤ 2*r := by simpa using Nat.mul_le_mul_left 2 hr
  have hp2 : 2 < p := ((two_le.trans hsmall).trans_lt
    (Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 3) hn) (by decide : 0 < 1))).trans_le hp
  obtain ⟨a, hap, _, haj⟩ := inverse_witness p j (lt_trans (by decide : 1 < 2) hp2) hj.symm
  have haj' : (a*j)%p = 1 := by simpa [Nat.mul_comm] using haj
  have ha : 1 ≤ a := by
    by_contra h
    have : a = 0 := by omega
    subst a
    simp at haj'
  by_cases han : a < n
  · have har : a = r := by
      by_contra hne
      have hh := hretained a ha han hne
      omega
    left
    simpa [har] using haj'
  · have hpan : p-a < n := by omega
    have hpa : 1 ≤ p-a := by omega
    have hlast := opposite_residue p a j (by omega) hap haj'
    have hpar : p-a = r := by
      by_contra hne
      have hh := hretained (p-a) hpa hpan hne
      omega
    right
    simpa [hpar] using hlast

theorem signed_inverse_coprime (p r j : ℕ) (hp : 2 < p) (hr : r < p)
    (h : (r*j)%p = 1 ∨ (r*j)%p = p-1) : Nat.Coprime r p := by
  rcases h with h | h
  · apply Nat.coprime_of_mul_modEq_one j
    change (r*j)%p = 1%p
    simpa [Nat.mod_eq_of_lt (show 1 < p by omega)] using h
  · have hop := opposite_last_to_one p r j hp hr h
    have hc : Nat.Coprime (p-r) p := by
      apply Nat.coprime_of_mul_modEq_one j
      change ((p-r)*j)%p = 1%p
      simpa [Nat.mod_eq_of_lt (show 1 < p by omega)] using hop
    exact (Nat.coprime_self_sub_left (by omega : r ≤ p)).1 hc

theorem signed_denominator_bound (n r p j : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r)
    (hsmall : 2*r ≤ n-1) (hp : n ≤ p)
    (hunit : (r*j)%p = 1 ∨ (r*j)%p = p-1)
    (hretained : ∀ v, 1 ≤ v → v < n → v ≠ r →
      2 ≤ (v*j)%p ∧ (v*j)%p + 2 ≤ p) : n+r ≤ p := by
  rcases hunit with h | h
  · exact denominator_bound n r p j hn hr hsmall (by omega) h hretained
  · have hop := opposite_last_to_one p r j (by omega) (by omega) h
    by_contra hnot
    have hv := hretained (p-r) (by omega) (by omega) (by omega)
    omega

theorem double_residue_negative (p r j : ℕ) (hp : 2 < p)
    (h : (r*j)%p = p-1) : ((2*r)*j)%p = p-2 := by
  have he : (2*r)*j = r*j + r*j := by simp [Nat.two_mul, Nat.add_mul]
  rw [he, Nat.add_mod, h]
  have hle : p ≤ p-1+(p-1) := by omega
  rw [Nat.mod_eq_sub_mod hle]
  have hs : p-1+(p-1)-p = p-2 := by omega
  rw [hs, Nat.mod_eq_of_lt (by omega)]

theorem signed_double_bound (n r p j q : ℕ) (hr : 1 ≤ r)
    (hsmall : 2*r ≤ n-1) (hp : 2 < p)
    (hunit : (r*j)%p = 1 ∨ (r*j)%p = p-1)
    (hq : ∀ v, 1 ≤ v → v < n → v ≠ r →
      q ≤ (v*j)%p ∧ (v*j)%p + q ≤ p) : q ≤ 2 := by
  have hv := hq (2*r) (by omega) (by omega) (by omega)
  rcases hunit with h | h
  · rw [double_residue p r j hp h] at hv
    omega
  · rw [double_residue_negative p r j hp h] at hv
    omega

theorem high_residue_certificate (n r p j q : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r)
    (hsmall : 2*r ≤ n-1) (hp : 1 ≤ p) (hpmax : p ≤ 2*(n-1))
    (hj : Nat.Coprime p j) (hq : 2 ≤ q)
    (hretained : ∀ v, 1 ≤ v → v < n → v ≠ r →
      q ≤ (v*j)%p ∧ (v*j)%p + q ≤ p) :
    leastDenominator n r (by omega) hr ≤ p ∧ q ≤ 2 := by
  have hpos : ∀ v, 1 ≤ v → v < n → v ≠ r → 1 ≤ (v*j)%p := by
    intro v h1 h2 h3
    have h := hretained v h1 h2 h3
    omega
  have hpn : n ≤ p := positive_residues_denominator n r p j hr hsmall hp hpos
  have hret2 : ∀ v, 1 ≤ v → v < n → v ≠ r →
      2 ≤ (v*j)%p ∧ (v*j)%p + 2 ≤ p := by
    intro v h1 h2 h3
    have h := hretained v h1 h2 h3
    omega
  have hi := inverse_is_removed n r p j hn hr hsmall hpn hpmax hj hret2
  have hcop := signed_inverse_coprime p r j (by omega) (by omega) hi
  have hd := signed_denominator_bound n r p j hn hr hsmall hpn hi hret2
  constructor
  · exact leastDenominator_minimal n r (by omega) hr p hd hcop.symm
  · exact signed_double_bound n r p j q hr hsmall (by omega) hi hretained

theorem mem_speeds {n r v : ℕ} : v ∈ speeds n r ↔ 1 ≤ v ∧ v < n ∧ v ≠ r := by
  simp only [speeds, List.mem_filter, List.mem_range', bne_iff_ne, Nat.one_mul]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hne⟩
    refine ⟨by omega, ?_, hne⟩
    omega
  · rintro ⟨hv, hvn, hne⟩
    exact ⟨⟨v-1, by omega, by omega⟩, hne⟩

theorem speeds_card (n r : ℕ) (hn : 4 ≤ n) (hr : 1 ≤ r) (hsmall : 2*r ≤ n-1) :
    1 < (speeds n r).toFinset.card := by
  apply Finset.one_lt_card.mpr
  by_cases h : r = 1
  · refine ⟨2, ?_, 3, ?_, by omega⟩ <;> apply List.mem_toFinset.mpr <;>
      apply mem_speeds.mpr <;> omega
  · refine ⟨1, ?_, 2*r, ?_, by omega⟩ <;> apply List.mem_toFinset.mpr <;>
      apply mem_speeds.mpr <;> omega

theorem rational_upper (n r p j : ℕ) (hn : 4 ≤ n) (hr : 1 ≤ r)
    (hsmall : 2*r ≤ n-1) (hp : 0 < p) (hpmax : p ≤ 2*(n-1))
    (hj : Nat.Coprime p j)
    (hpositive : 0 < Loneliness.clearance (speeds n r) ((j : ℝ)/p)) :
    Loneliness.clearance (speeds n r) ((j : ℝ)/p) ≤
      (2 : ℝ) / leastDenominator n r (by omega) hr := by
  classical
  let ds := speeds n r
  have hc : 1 < ds.toFinset.card := speeds_card n r hn hr hsmall
  have hD : ds.toFinset.Nonempty := Finset.card_pos.mp (by omega)
  let q := ds.toFinset.inf' hD (fun v => Loneliness.PairSum.folded v j p)
  obtain ⟨v, hv, hvq⟩ := Finset.exists_mem_eq_inf' hD (fun v => Loneliness.PairSum.folded v j p)
  have hvlist : v ∈ ds := by simpa using hv
  have hcle : Loneliness.clearance ds ((j : ℝ)/p) ≤ (q : ℝ)/p := by
    have h := Loneliness.clearance_le_of_mem hvlist ((j : ℝ)/p)
    rw [← Loneliness.PairSum.distance_eq_distance] at h
    rw [Loneliness.PairSum.distance_rational] at h
    simpa [q, hvq] using h
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hqpos : 1 ≤ q := by
    by_contra h
    have : q = 0 := by omega
    rw [this] at hcle
    simp at hcle
    linarith
  have hfold : ∀ v, 1 ≤ v → v < n → v ≠ r →
      q ≤ (v*j)%p ∧ (v*j)%p + q ≤ p := by
    intro w hw hwn hwr
    have hmem : w ∈ ds.toFinset := by
      apply List.mem_toFinset.mpr
      exact mem_speeds.mpr ⟨hw, hwn, hwr⟩
    have hi : q ≤ Loneliness.PairSum.folded w j p := Finset.inf'_le _ hmem
    simp only [Loneliness.PairSum.folded, le_min_iff] at hi
    have hm := Nat.mod_lt (w*j) hp
    omega
  have hpos : ∀ v, 1 ≤ v → v < n → v ≠ r → 1 ≤ (v*j)%p := by
    intro w hw hwn hwr
    have h := hfold w hw hwn hwr
    omega
  have hpn := positive_residues_denominator n r p j hr hsmall hp hpos
  have hDen := Nat.find_spec (coprime_in_window n r (by omega) hr)
  have hDenUpper : leastDenominator n r (by omega) hr ≤ 2*p := by
    change Nat.find (coprime_in_window n r (by omega) hr) ≤ 2*p
    omega
  have hDenPos : (0 : ℝ) < leastDenominator n r (by omega) hr := by
    exact_mod_cast (show 0 < leastDenominator n r (by omega) hr from by
      have h := leastDenominator_spec n r (by omega) hr
      omega)
  by_cases hq : q ≤ 1
  · have hqR : (q : ℝ) ≤ 1 := by exact_mod_cast hq
    have hdR : (leastDenominator n r (by omega) hr : ℝ) ≤ 2*(p : ℝ) := by exact_mod_cast hDenUpper
    have hbound : (q : ℝ)/p ≤ 2/leastDenominator n r (by omega) hr := by
      apply (div_le_div_iff₀ hpr hDenPos).2
      nlinarith
    exact hcle.trans hbound
  · have cert := high_residue_certificate n r p j q (by omega) hr hsmall hp hpmax hj (by omega) hfold
    have hqR : (q : ℝ) ≤ 2 := by exact_mod_cast cert.2
    have hdR : (leastDenominator n r (by omega) hr : ℝ) ≤ p := by exact_mod_cast cert.1
    have hbound : (q : ℝ)/p ≤ 2/leastDenominator n r (by omega) hr := by
      apply (div_le_div_iff₀ hpr hDenPos).2
      nlinarith
    exact hcle.trans hbound

theorem small_deletion_upper (n r : ℕ) (hn : 4 ≤ n) (hr : 1 ≤ r)
    (hsmall : 2*r ≤ n-1) :
    Loneliness.value (speeds n r) ≤ (2 : ℝ) / leastDenominator n r (by omega) hr := by
  have hcard := speeds_card n r hn hr hsmall
  have hpos : ∀ d ∈ speeds n r, 0 < d := by
    intro d hd
    have h := mem_speeds.mp hd
    omega
  obtain ⟨a, ha, b, hb, _, k, _, hvalue, _⟩ :=
    Loneliness.exists_pair_sum_maximum (speeds n r) hcard hpos
  have hab : 0 < a+b := by have := hpos a ha; omega
  let g := Nat.gcd k (a+b)
  let p := (a+b)/g
  let j := k/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right k hab
  have hp : 0 < p := Nat.div_gcd_pos_of_pos_right k hab
  have hcop : Nat.Coprime p j := (Nat.coprime_div_gcd_div_gcd hg).symm
  have hmulj : j*g = k := Nat.div_mul_cancel (Nat.gcd_dvd_left k (a+b))
  have hmulp : p*g = a+b := Nat.div_mul_cancel (Nat.gcd_dvd_right k (a+b))
  have hfrac : (j : ℝ)/p = (k : ℝ)/(a+b : ℕ) := by
    have hgr : (g : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hg)
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
    have h1 : (j : ℝ)*g = k := by exact_mod_cast hmulj
    have h2 : (p : ℝ)*g = (a+b : ℕ) := by exact_mod_cast hmulp
    rw [← h1, ← h2]
    field_simp
  have haBound := (mem_speeds.mp ha).2.1
  have hbBound := (mem_speeds.mp hb).2.1
  have hpmax : p ≤ 2*(n-1) := by
    have hpg : p ≤ p*g := Nat.le_mul_of_pos_right p hg
    omega
  have hvpos : 0 < Loneliness.value (speeds n r) := by
    have hl := small_deletion_lower n r (by omega) hr
    have hd : (0 : ℝ) < leastDenominator n r (by omega) hr := by
      exact_mod_cast (show 0 < leastDenominator n r (by omega) hr from by
        have h := leastDenominator_spec n r (by omega) hr
        omega)
    have : (0 : ℝ) < 2 / leastDenominator n r (by omega) hr := by positivity
    linarith
  have htpos : 0 < Loneliness.clearance (speeds n r) ((j : ℝ)/p) := by
    rw [hfrac, hvalue]
    exact hvpos
  have hu := rational_upper n r p j hn hr hsmall hp hpmax hcop htpos
  rw [hfrac, hvalue] at hu
  exact hu

theorem small_deletion_exact (n r : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r)
    (hsmall : 2*r ≤ n-1) :
    Loneliness.value (speeds n r) = (2 : ℝ) / leastDenominator n r (by omega) hr := by
  apply le_antisymm
  · by_cases hn4 : 4 ≤ n
    · exact small_deletion_upper n r hn4 hr hsmall
    · have hn3 : n = 3 := by omega
      have hr1 : r = 1 := by omega
      subst n
      subst r
      have hlow := leastDenominator_spec 3 1 (by omega) (by omega)
      have hupp := leastDenominator_minimal 3 1 (by omega) (by omega) 4 (by omega) (by simp)
      have hd : leastDenominator 3 1 (by omega) (by omega) = 4 := by omega
      rw [hd]
      norm_num
      exact Loneliness.value_le (fun t _ => Loneliness.clearance_le_half _ t)
  · exact small_deletion_lower n r hn hr

end ZhangDeletion
