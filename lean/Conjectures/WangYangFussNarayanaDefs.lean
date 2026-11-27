import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Fuss–Narayana Matrices and Exact Product Identities

Defines the six Fuss–Narayana arrays from Conjecture 4.1 of Yi Wang and Arthur L. B. Yang,
*Total positivity of Narayana matrices*, Discrete Mathematics 341 (2018), and proves the
exact product identities (2), (3), and (4) from `results/wang-yang-fuss-narayana/proof.md`:
- `matB`, `matA`: the ordinary Type B and Type A triangles;
- `matBRev`, `matARev`: their row reversals;
- `matBSquare`, `matASquare`: the Type B and Type A squares `B(n + k, k)` and `A(n + k, k)`.
-/

namespace Conjectures.WangYangFussNarayana

open Finset
open scoped BigOperators

/-- Type B Fuss–Narayana entry `B(n, k) = C(n, k) * C(m * n, n - k)` (zero when `k > n`). -/
def fussNarayanaB (m n k : ℕ) : ℝ :=
  if k ≤ n then (Nat.choose n k : ℝ) * (Nat.choose (m * n) (n - k) : ℝ) else 0

/-- Type A Fuss–Narayana entry `A(n, k) = (1 / (n + 1)) * C(n + 1, k) * C(m * (n + 1), n - k)`
(zero when `k > n`). -/
noncomputable def fussNarayanaA (m n k : ℕ) : ℝ :=
  if k ≤ n then
    ((Nat.choose (n + 1) k : ℝ) * (Nat.choose (m * (n + 1)) (n - k) : ℝ)) / ((n + 1 : ℕ) : ℝ)
  else 0

/-- Ordinary Type B Fuss–Narayana triangle `[B(n, k)]_{n, k ≥ 0}`. -/
def matB (m : ℕ) : Matrix ℕ ℕ ℝ := fun n k => fussNarayanaB m n k

/-- Ordinary Type A Fuss–Narayana triangle `[A(n, k)]_{n, k ≥ 0}`. -/
noncomputable def matA (m : ℕ) : Matrix ℕ ℕ ℝ := fun n k => fussNarayanaA m n k

/-- Row-reversed Type B Fuss–Narayana triangle `[B(n, n - k)]_{n, k ≥ 0}` (zero for `k > n`). -/
def matBRev (m : ℕ) : Matrix ℕ ℕ ℝ := fun n k =>
  if k ≤ n then fussNarayanaB m n (n - k) else 0

/-- Row-reversed Type A Fuss–Narayana triangle `[A(n, n - k)]_{n, k ≥ 0}` (zero for `k > n`). -/
noncomputable def matARev (m : ℕ) : Matrix ℕ ℕ ℝ := fun n k =>
  if k ≤ n then fussNarayanaA m n (n - k) else 0

/-- Type B Fuss–Narayana square `[B(n + k, k)]_{n, k ≥ 0}`. -/
def matBSquare (m : ℕ) : Matrix ℕ ℕ ℝ := fun n k => fussNarayanaB m (n + k) k

/-- Type A Fuss–Narayana square `[A(n + k, k)]_{n, k ≥ 0}`. -/
noncomputable def matASquare (m : ℕ) : Matrix ℕ ℕ ℝ := fun n k => fussNarayanaA m (n + k) k

/-- Unified family `entry m s n k`: `s = 0` is Type B, `s = 1` is Type A. -/
noncomputable def fussEntry (m s n k : ℕ) : ℝ :=
  if k ≤ n then
    ((Nat.choose (n + s) k : ℝ) * (Nat.choose (m * (n + s)) (n - k) : ℝ)) /
      (if s = 0 then (1 : ℝ) else ((n + 1 : ℕ) : ℝ))
  else 0

theorem fussEntry_zero (m n k : ℕ) : fussEntry m 0 n k = fussNarayanaB m n k := by
  simp [fussEntry, fussNarayanaB]

theorem fussEntry_one (m n k : ℕ) : fussEntry m 1 n k = fussNarayanaA m n k := by
  simp [fussEntry, fussNarayanaA]

theorem fussNarayanaB_eq (m n k : ℕ) :
    fussNarayanaB m n k = (Nat.choose n k : ℝ) * (Nat.choose (m * n) (n - k) : ℝ) := by
  unfold fussNarayanaB
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]
    simp

/-- First-column entries are strictly positive for `m ≥ 1`. -/
theorem fussEntry_col_zero_pos {m : ℕ} (hm : 1 ≤ m) (s n : ℕ) :
    0 < fussEntry m s n 0 := by
  have hle : n ≤ m * (n + s) := by nlinarith
  have hc : 0 < Nat.choose (m * (n + s)) n := Nat.choose_pos hle
  unfold fussEntry
  simp only [Nat.zero_le, ite_true, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul]
  split_ifs
  · simp [Nat.cast_pos.mpr hc]
  · exact div_pos (Nat.cast_pos.mpr hc) (by positivity)

/-! ### Unified square array and ratio identity (2) -/

/-- Unified square entry `S_s(n, k) = C(n + k, n) * C(m * (n + k + s), n)`. -/
def squareUnified (m s n k : ℕ) : ℝ :=
  (Nat.choose (n + k) n : ℝ) * (Nat.choose (m * (n + k + s)) n : ℝ)

theorem squareUnified_pos {m : ℕ} (hm : 1 ≤ m) (s n k : ℕ) :
    0 < squareUnified m s n k := by
  have h1 : 0 < Nat.choose (n + k) n := Nat.choose_pos (Nat.le_add_right n k)
  have h2 : 0 < Nat.choose (m * (n + k + s)) n := Nat.choose_pos (by nlinarith)
  exact mul_pos (Nat.cast_pos.mpr h1) (Nat.cast_pos.mpr h2)

theorem matBSquare_eq_squareUnified (m n k : ℕ) :
    matBSquare m n k = squareUnified m 0 n k := by
  simp only [matBSquare, fussNarayanaB, Nat.le_add_left, ite_true, Nat.add_sub_cancel,
    squareUnified, Nat.add_zero]
  rw [Nat.choose_symm_add]

theorem matASquare_eq_squareUnified (m n k : ℕ) :
    matASquare m n k = squareUnified m 1 n k / ((n + 1 : ℕ) : ℝ) := by
  simp only [matASquare, fussNarayanaA, Nat.le_add_left, ite_true, Nat.add_sub_cancel,
    squareUnified]
  have hnat : (n + 1) * Nat.choose (n + k + 1) k = (n + k + 1) * Nat.choose (n + k) n := by
    have h1 : Nat.choose (n + k + 1) k = Nat.choose (n + k + 1) (n + 1) := by
      have hsym := Nat.choose_symm (by omega : k ≤ n + k + 1)
      have hsub : n + k + 1 - k = n + 1 := by omega
      rw [hsub] at hsym
      exact hsym.symm
    rw [h1, Nat.add_one_mul_choose_eq]
    ring
  have hreal : ((n + 1 : ℕ) : ℝ) * (Nat.choose (n + k + 1) k : ℝ) =
      ((n + k + 1 : ℕ) : ℝ) * (Nat.choose (n + k) n : ℝ) := by
    exact_mod_cast hnat
  have hne1 : ((n + k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hne2 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [div_eq_div_iff hne1 hne2]
  calc
    (Nat.choose (n + k + 1) k : ℝ) * (Nat.choose (m * (n + k + 1)) n : ℝ) * ((n + 1 : ℕ) : ℝ)
        = (((n + 1 : ℕ) : ℝ) * (Nat.choose (n + k + 1) k : ℝ)) *
            (Nat.choose (m * (n + k + 1)) n : ℝ) := by ring
    _ = (((n + k + 1 : ℕ) : ℝ) * (Nat.choose (n + k) n : ℝ)) *
            (Nat.choose (m * (n + k + 1)) n : ℝ) := by rw [hreal]
    _ = (Nat.choose (n + k) n : ℝ) * (Nat.choose (m * (n + k + 1)) n : ℝ) *
            ((n + k + 1 : ℕ) : ℝ) := by ring

/-- Helper: stepping the top parameter of a binomial coefficient by `1`. -/
theorem choose_succ_left_mul_sub (N n : ℕ) (h : n ≤ N) :
    (N + 1 - n) * Nat.choose (N + 1) n = (N + 1) * Nat.choose N n := by
  have h1 := Nat.add_one_mul_choose_eq N (N - n)
  have hsym1 : Nat.choose N (N - n) = Nat.choose N n := Nat.choose_symm h
  have hsym2 : Nat.choose (N + 1) (N - n + 1) = Nat.choose (N + 1) n := by
    have hle : N - n + 1 ≤ N + 1 := by omega
    have hsub : N + 1 - (N - n + 1) = n := by omega
    have hsym := Nat.choose_symm hle
    rw [hsub] at hsym
    exact hsym.symm
  rw [hsym1, hsym2] at h1
  have h2 : N - n + 1 = N + 1 - n := by omega
  rw [h2] at h1
  linarith

/-- Helper: ratio of `C(N + m, n) / C(N, n)` as a product of `m` fractions. -/
theorem choose_add_div_choose (N n m : ℕ) (h : n ≤ N) :
    (Nat.choose (N + m) n : ℝ) / (Nat.choose N n : ℝ) =
      ∏ r ∈ Finset.range m,
        ((N + r + 1 : ℕ) : ℝ) / ((N + r + 1 - n : ℕ) : ℝ) := by
  induction m with
  | zero =>
    have hpos : (Nat.choose N n : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Nat.choose_pos h)).ne'
    simp [div_self hpos]
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih]
    have hstep : (Nat.choose (N + m + 1) n : ℝ) * ((N + m + 1 - n : ℕ) : ℝ) =
        (Nat.choose (N + m) n : ℝ) * ((N + m + 1 : ℕ) : ℝ) := by
      have hnat := choose_succ_left_mul_sub (N + m) n (by omega)
      have hreal : ((N + m + 1 - n : ℕ) : ℝ) * (Nat.choose (N + m + 1) n : ℝ) =
          ((N + m + 1 : ℕ) : ℝ) * (Nat.choose (N + m) n : ℝ) := by
        exact_mod_cast hnat
      linarith
    have hc0 : (Nat.choose N n : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Nat.choose_pos h)).ne'
    have hden : ((N + m + 1 - n : ℕ) : ℝ) ≠ 0 := by
      have : 0 < N + m + 1 - n := by omega
      positivity
    rw [← Nat.add_assoc, div_mul_div_comm, div_eq_div_iff hc0 (mul_ne_zero hc0 hden)]
    calc
      (Nat.choose (N + m + 1) n : ℝ) * ((Nat.choose N n : ℝ) * ((N + m + 1 - n : ℕ) : ℝ))
          = (Nat.choose N n : ℝ) *
              ((Nat.choose (N + m + 1) n : ℝ) * ((N + m + 1 - n : ℕ) : ℝ)) := by ring
      _ = (Nat.choose N n : ℝ) *
              ((Nat.choose (N + m) n : ℝ) * ((N + m + 1 : ℕ) : ℝ)) := by rw [hstep]
      _ = (Nat.choose (N + m) n : ℝ) * ((N + m + 1 : ℕ) : ℝ) * (Nat.choose N n : ℝ) := by ring

/-- Exact square ratio identity (Formula (2) in `proof.md`). -/
theorem squareUnified_succ_col {m : ℕ} (hm : 1 ≤ m) (s n k : ℕ) :
    squareUnified m s n (k + 1) / squareUnified m s n k =
      (∏ r ∈ Finset.range m,
        ((n : ℝ) + ((k + s : ℕ) : ℝ) + ((r + 1 : ℕ) : ℝ) / (m : ℝ)) /
          (((m - 1 : ℕ) : ℝ) / (m : ℝ) * (n : ℝ) +
            ((k + s : ℕ) : ℝ) + ((r + 1 : ℕ) : ℝ) / (m : ℝ))) *
        (((n : ℝ) + ((k + 1 : ℕ) : ℝ)) / ((k + 1 : ℕ) : ℝ)) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
  have hfirst :
      (Nat.choose (n + (k + 1)) n : ℝ) / (Nat.choose (n + k) n : ℝ) =
        ((n : ℝ) + ((k + 1 : ℕ) : ℝ)) / ((k + 1 : ℕ) : ℝ) := by
    have hnat : (k + 1) * Nat.choose (n + k + 1) n = (n + k + 1) * Nat.choose (n + k) n := by
      simpa [show n + k + 1 - n = k + 1 by omega] using
        choose_succ_left_mul_sub (n + k) n (Nat.le_add_right n k)
    have hreal : ((k + 1 : ℕ) : ℝ) * (Nat.choose (n + k + 1) n : ℝ) =
        ((n + k + 1 : ℕ) : ℝ) * (Nat.choose (n + k) n : ℝ) := by
      exact_mod_cast hnat
    have hc : (Nat.choose (n + k) n : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_right n k))).ne'
    have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show n + (k + 1) = n + k + 1 by omega, div_eq_div_iff hc hk1]
    have hadd : (n : ℝ) + ((k + 1 : ℕ) : ℝ) = ((n + k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hadd]
    linarith
  have hsecond :
      (Nat.choose (m * (n + (k + 1) + s)) n : ℝ) / (Nat.choose (m * (n + k + s)) n : ℝ) =
        ∏ r ∈ Finset.range m,
          ((n : ℝ) + ((k + s : ℕ) : ℝ) + ((r + 1 : ℕ) : ℝ) / (m : ℝ)) /
            (((m - 1 : ℕ) : ℝ) / (m : ℝ) * (n : ℝ) +
              ((k + s : ℕ) : ℝ) + ((r + 1 : ℕ) : ℝ) / (m : ℝ)) := by
    rw [show m * (n + (k + 1) + s) = m * (n + k + s) + m by ring]
    rw [choose_add_div_choose (m * (n + k + s)) n m (by nlinarith)]
    refine Finset.prod_congr rfl fun r _ => ?_
    have hsub_le : n ≤ m * (n + k + s) + r + 1 := by nlinarith
    have hcast_m : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm, Nat.cast_one]
    have hcast_sub : ((m * (n + k + s) + r + 1 - n : ℕ) : ℝ) =
        ((m * (n + k + s) + r + 1 : ℕ) : ℝ) - (n : ℝ) := by
      rw [Nat.cast_sub hsub_le]
    rw [hcast_m, hcast_sub]
    have hd1 : ((m * (n + k + s) + r + 1 : ℕ) : ℝ) - (n : ℝ) ≠ 0 := by
      have : n < m * (n + k + s) + r + 1 := by nlinarith
      have hlt : (n : ℝ) < ((m * (n + k + s) + r + 1 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have hd2 : ((m : ℝ) - 1) / (m : ℝ) * (n : ℝ) + ((k + s : ℕ) : ℝ) +
        ((r + 1 : ℕ) : ℝ) / (m : ℝ) ≠ 0 := by
      have h1 : (0 : ℝ) ≤ ((m : ℝ) - 1) / (m : ℝ) * (n : ℝ) := by
        have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
          have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          linarith
        positivity
      have h2 : (0 : ℝ) ≤ ((k + s : ℕ) : ℝ) := by positivity
      have h3 : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) / (m : ℝ) := by positivity
      linarith
    rw [div_eq_div_iff hd1 hd2]
    field_simp [hm_ne]
    push_cast
    ring
  unfold squareUnified
  rw [mul_div_mul_comm, hfirst, hsecond, mul_comm]

/-! ### Ordinary triangle product identity (3) -/

/-- Exact ordinary triangle product formula (Formula (3) in `proof.md`):
`k! * entry(m, s, n, k) = entry(m, s, n, 0) * ∏_{j < k} ((n - j + s)(n - j)) / ((m - 1)n + ms + j + 1)`.
Valid for ALL `n, k : ℕ` (including `k > n`, where both sides are zero). -/
theorem ordinary_product_identity {m : ℕ} (hm : 1 ≤ m) (s n k : ℕ) :
    (k.factorial : ℝ) * fussEntry m s n k =
      fussEntry m s n 0 *
        ∏ j ∈ Finset.range k,
          ((((n : ℝ) - (j : ℝ) + (s : ℝ)) * ((n : ℝ) - (j : ℝ))) /
            (((m - 1 : ℕ) : ℝ) * (n : ℝ) + (m : ℝ) * (s : ℝ) + (j : ℝ) + 1)) := by
  by_cases hkn : k ≤ n
  · induction k with
    | zero =>
      simp
    | succ k ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ← ih (by omega)]
      have hden_pos :
          0 < ((m - 1 : ℕ) : ℝ) * (n : ℝ) + (m : ℝ) * (s : ℝ) + (k : ℝ) + 1 := by
        positivity
      have hden_ne :
          ((m - 1 : ℕ) : ℝ) * (n : ℝ) + (m : ℝ) * (s : ℝ) + (k : ℝ) + 1 ≠ 0 := hden_pos.ne'
      rw [mul_div_assoc', eq_div_iff hden_ne]
      -- Cancel common divisor of `fussEntry` and check the binomial step in `ℕ`.
      have hstep_nat1 :
          (k + 1) * Nat.choose (n + s) (k + 1) = (n + s - k) * Nat.choose (n + s) k := by
        have := Nat.choose_succ_right_eq (n + s) k
        linarith
      have hstep_nat2 :
          ((m - 1) * n + m * s + k + 1) * Nat.choose (m * (n + s)) (n - (k + 1)) =
            (n - k) * Nat.choose (m * (n + s)) (n - k) := by
        have h1 := Nat.choose_succ_right_eq (m * (n + s)) (n - (k + 1))
        have hsub1 : n - (k + 1) + 1 = n - k := by omega
        have hsub2 : m * (n + s) - (n - (k + 1)) = (m - 1) * n + m * s + k + 1 := by
          have : m * (n + s) = (m - 1) * n + n + m * s := by
            cases m with
            | zero => omega
            | succ m' => simp only [Nat.add_sub_cancel]; ring
          omega
        rw [hsub1, hsub2] at h1
        linarith
      have hreal1 :
          ((k + 1 : ℕ) : ℝ) * (Nat.choose (n + s) (k + 1) : ℝ) =
            ((n : ℝ) - (k : ℝ) + (s : ℝ)) * (Nat.choose (n + s) k : ℝ) := by
        have hcast : ((n + s - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) + (s : ℝ) := by
          rw [Nat.cast_sub (by omega : k ≤ n + s)]
          push_cast; ring
        rw [← hcast]
        exact_mod_cast hstep_nat1
      have hreal2 :
          (((m - 1 : ℕ) : ℝ) * (n : ℝ) + (m : ℝ) * (s : ℝ) + (k : ℝ) + 1) *
              (Nat.choose (m * (n + s)) (n - (k + 1)) : ℝ) =
            ((n : ℝ) - (k : ℝ)) * (Nat.choose (m * (n + s)) (n - k) : ℝ) := by
        have hcast1 : (((m - 1) * n + m * s + k + 1 : ℕ) : ℝ) =
            ((m - 1 : ℕ) : ℝ) * (n : ℝ) + (m : ℝ) * (s : ℝ) + (k : ℝ) + 1 := by
          push_cast; ring
        have hcast2 : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
          rw [Nat.cast_sub (by omega : k ≤ n)]
        rw [← hcast1, ← hcast2]
        exact_mod_cast hstep_nat2
      unfold fussEntry
      simp only [hkn, show k ≤ n by omega, ite_true, Nat.factorial_succ, Nat.cast_mul]
      set divS : ℝ := if s = 0 then (1 : ℝ) else ((n + 1 : ℕ) : ℝ)
      calc
        ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) *
            ((Nat.choose (n + s) (k + 1) : ℝ) * (Nat.choose (m * (n + s)) (n - (k + 1)) : ℝ) / divS) *
            (((m - 1 : ℕ) : ℝ) * (n : ℝ) + (m : ℝ) * (s : ℝ) + (k : ℝ) + 1)
            = (k.factorial : ℝ) / divS *
                ((((k + 1 : ℕ) : ℝ) * (Nat.choose (n + s) (k + 1) : ℝ)) *
                  ((((m - 1 : ℕ) : ℝ) * (n : ℝ) + (m : ℝ) * (s : ℝ) + (k : ℝ) + 1) *
                    (Nat.choose (m * (n + s)) (n - (k + 1)) : ℝ))) := by ring
        _ = (k.factorial : ℝ) / divS *
                ((((n : ℝ) - (k : ℝ) + (s : ℝ)) * (Nat.choose (n + s) k : ℝ)) *
                  (((n : ℝ) - (k : ℝ)) * (Nat.choose (m * (n + s)) (n - k) : ℝ))) := by
              rw [hreal1, hreal2]
        _ = (k.factorial : ℝ) *
              ((Nat.choose (n + s) k : ℝ) * (Nat.choose (m * (n + s)) (n - k) : ℝ) / divS) *
              (((n : ℝ) - (k : ℝ) + (s : ℝ)) * ((n : ℝ) - (k : ℝ))) := by ring
  · -- When `k > n`, both sides are 0 because the `j = n` factor vanishes.
    have hlt : n < k := Nat.lt_of_not_ge hkn
    have hlhs : fussEntry m s n k = 0 := by simp [fussEntry, hkn]
    rw [hlhs, mul_zero]
    symm
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_range.mpr hlt) ?_)
    simp

/-! ### Reversed triangle product identity (4) -/

/-- Falling factorial product `∏_{j < k} (n - j) = k! * C(n, k)` over `ℝ`, valid for all `n, k`. -/
theorem prod_sub_eq_factorial_mul_choose (n k : ℕ) :
    (∏ j ∈ Finset.range k, ((n : ℝ) - (j : ℝ))) = (k.factorial : ℝ) * (Nat.choose n k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ, Nat.cast_mul]
    by_cases hkn : k ≤ n
    · have hnat := Nat.choose_succ_right_eq n k
      have hreal : (Nat.choose n (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
          (Nat.choose n k : ℝ) * ((n : ℝ) - (k : ℝ)) := by
        rw [← Nat.cast_sub hkn]
        exact_mod_cast hnat
      calc
        (k.factorial : ℝ) * (Nat.choose n k : ℝ) * ((n : ℝ) - (k : ℝ))
            = (k.factorial : ℝ) * ((Nat.choose n k : ℝ) * ((n : ℝ) - (k : ℝ))) := by ring
        _ = (k.factorial : ℝ) * ((Nat.choose n (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ)) := by rw [hreal]
        _ = ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) * (Nat.choose n (k + 1) : ℝ) := by ring
    · have h1 : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have h2 : Nat.choose n (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h1, h2]

theorem matBRev_eq (m n k : ℕ) :
    matBRev m n k = (Nat.choose n k : ℝ) * (Nat.choose (m * n) k : ℝ) := by
  unfold matBRev fussNarayanaB
  by_cases hkn : k ≤ n
  · simp only [hkn, Nat.sub_le, ite_true, Nat.sub_sub_self hkn]
    rw [Nat.choose_symm hkn]
  · simp only [hkn, ite_false]
    rw [Nat.choose_eq_zero_of_lt (by omega : n < k)]
    simp

theorem matARev_eq (m n k : ℕ) :
    matARev m n k =
      ((Nat.choose n k : ℝ) * (Nat.choose (m * (n + 1)) k : ℝ)) / ((k + 1 : ℕ) : ℝ) := by
  unfold matARev fussNarayanaA
  by_cases hkn : k ≤ n
  · simp only [hkn, Nat.sub_le, ite_true, Nat.sub_sub_self hkn]
    have hnat : (k + 1) * Nat.choose (n + 1) (n - k) = (n + 1) * Nat.choose n k := by
      have hsym : Nat.choose (n + 1) (n - k) = Nat.choose (n + 1) (k + 1) := by
        have := Nat.choose_symm (by omega : n - k ≤ n + 1)
        have hsub : n + 1 - (n - k) = k + 1 := by omega
        rw [hsub] at this
        exact this.symm
      rw [hsym, Nat.add_one_mul_choose_eq]
      ring
    have hreal : ((k + 1 : ℕ) : ℝ) * (Nat.choose (n + 1) (n - k) : ℝ) =
        ((n + 1 : ℕ) : ℝ) * (Nat.choose n k : ℝ) := by
      exact_mod_cast hnat
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [div_eq_div_iff hn1 hk1]
    calc
      (Nat.choose (n + 1) (n - k) : ℝ) * (Nat.choose (m * (n + 1)) k : ℝ) * ((k + 1 : ℕ) : ℝ)
          = (((k + 1 : ℕ) : ℝ) * (Nat.choose (n + 1) (n - k) : ℝ)) *
              (Nat.choose (m * (n + 1)) k : ℝ) := by ring
      _ = (((n + 1 : ℕ) : ℝ) * (Nat.choose n k : ℝ)) *
              (Nat.choose (m * (n + 1)) k : ℝ) := by rw [hreal]
      _ = (Nat.choose n k : ℝ) * (Nat.choose (m * (n + 1)) k : ℝ) * ((n + 1 : ℕ) : ℝ) := by ring
  · simp only [hkn, ite_false]
    rw [Nat.choose_eq_zero_of_lt (by omega : n < k)]
    simp

/-- Exact reversed triangle product identity (Formula (4) in `proof.md`). -/
theorem reversed_product_identity {m : ℕ} (hm : 1 ≤ m) (s n k : ℕ) :
    (∏ j ∈ Finset.range k, (((n : ℝ) - (j : ℝ)) * ((n : ℝ) - ((j : ℝ) / (m : ℝ) - (s : ℝ))))) =
      ((k.factorial : ℝ) ^ 2 / (m : ℝ) ^ k) *
        ((Nat.choose n k : ℝ) * (Nat.choose (m * (n + s)) k : ℝ)) := by
  have hm_ne : (m : ℝ) ≠ 0 := by positivity
  rw [Finset.prod_mul_distrib, prod_sub_eq_factorial_mul_choose n k]
  have h2 :
      (∏ j ∈ Finset.range k, ((n : ℝ) - ((j : ℝ) / (m : ℝ) - (s : ℝ)))) =
        (∏ j ∈ Finset.range k, (((m * (n + s) : ℕ) : ℝ) - (j : ℝ))) / (m : ℝ) ^ k := by
    rw [show (m : ℝ) ^ k = ∏ _j ∈ Finset.range k, (m : ℝ) by simp]
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    field_simp [hm_ne]
    push_cast
    ring
  rw [h2, prod_sub_eq_factorial_mul_choose (m * (n + s)) k]
  ring

end Conjectures.WangYangFussNarayana
