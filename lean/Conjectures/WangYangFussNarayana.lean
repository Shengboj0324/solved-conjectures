import Conjectures.WangYangFussNarayanaDefs
import Conjectures.WangYangFussNarayanaCriteria
import Mathlib.Tactic.GCongr

/-!
# Wang–Yang's Fuss–Narayana Conjecture (Conjecture 4.1)

Complete Lean 4 formalization of Conjecture 4.1 of Yi Wang and Arthur L. B. Yang,
*Total positivity of Narayana matrices*, Discrete Mathematics **341** (2018),
following `results/wang-yang-fuss-narayana/proof.md`.

For every integer `m ≥ 2` (in fact every `m ≥ 1`), all six arrays have their conjectured
positivity properties on arbitrary finite row and column selections:
1. `matB_isTotallyNonneg`: `[B(n, k)]` is totally nonnegative (TN).
2. `matA_isTotallyNonneg`: `[A(n, k)]` is totally nonnegative (TN).
3. `matBRev_isTotallyNonneg`: `[B(n, n - k)]` is totally nonnegative (TN).
4. `matARev_isTotallyNonneg`: `[A(n, n - k)]` is totally nonnegative (TN).
5. `matBSquare_isStrictlyTotallyPos`: `[B(n + k, k)]` is strictly totally positive (STP).
6. `matASquare_isStrictlyTotallyPos`: `[A(n + k, k)]` is strictly totally positive (STP).
-/

namespace Conjectures.WangYangFussNarayana

open Matrix Filter Topology Finset
open scoped BigOperators

/-! ### Part 1: The two squares are strictly totally positive -/

section Squares

/-- Parameter sequences `(t, a, b)` for the expanded square matrix with `m + 1` factors per column. -/
private noncomputable def sqT (m s q : ℕ) : ℝ :=
  let k := q / (m + 1)
  let r := q % (m + 1)
  if r < m then -(((k + s : ℕ) : ℝ) + ((r + 1 : ℕ) : ℝ) / (m : ℝ))
  else -((k + 1 : ℕ) : ℝ)

private noncomputable def sqA (m q : ℕ) : ℝ :=
  let r := q % (m + 1)
  if r < m then ((m - 1 : ℕ) : ℝ) / (m : ℝ) else 0

private noncomputable def sqB (m s q : ℕ) : ℝ :=
  let k := q / (m + 1)
  let r := q % (m + 1)
  if r < m then ((k + s : ℕ) : ℝ) + ((r + 1 : ℕ) : ℝ) / (m : ℝ)
  else ((k + 1 : ℕ) : ℝ)

private theorem sqB_pos {m : ℕ} (hm : 1 ≤ m) (s q : ℕ) : 0 < sqB m s q := by
  unfold sqB
  dsimp only
  split_ifs <;> positivity

private theorem sqT_neg {m : ℕ} (hm : 1 ≤ m) (s q : ℕ) : sqT m s q < 0 := by
  unfold sqT
  dsimp only
  split_ifs <;> linarith [show (0 : ℝ) < ((q / (m + 1) + s : ℕ) : ℝ) +
    ((q % (m + 1) + 1 : ℕ) : ℝ) / (m : ℝ) by positivity,
    show (0 : ℝ) < ((q / (m + 1) + 1 : ℕ) : ℝ) by positivity]

private theorem sqA_nonneg (m q : ℕ) : 0 ≤ sqA m q := by
  unfold sqA
  dsimp only
  split_ifs <;> positivity

private theorem sq_den_pos_nonneg {m : ℕ} (hm : 1 ≤ m) (s q : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < sqA m q * x + sqB m s q := by
  have ha := sqA_nonneg m q
  have hb := sqB_pos hm s q
  nlinarith

private theorem sq_cross_pos {m : ℕ} (hm : 1 ≤ m) (s q₁ q₂ : ℕ) (hq : q₁ ≤ q₂) :
    0 < sqA m q₂ * sqT m s q₁ + sqB m s q₂ := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  set k₁ := q₁ / (m + 1)
  set r₁ := q₁ % (m + 1)
  set k₂ := q₂ / (m + 1)
  set r₂ := q₂ % (m + 1)
  have hdiv1 : q₁ = (m + 1) * k₁ + r₁ := (Nat.div_add_mod q₁ (m + 1)).symm
  have hdiv2 : q₂ = (m + 1) * k₂ + r₂ := (Nat.div_add_mod q₂ (m + 1)).symm
  have hr1_lt : r₁ < m + 1 := Nat.mod_lt q₁ (by omega)
  have hr2_lt : r₂ < m + 1 := Nat.mod_lt q₂ (by omega)
  have hk_le : k₁ ≤ k₂ := Nat.div_le_div_right hq
  unfold sqA sqT sqB
  dsimp only
  change 0 < (if r₂ < m then ((m - 1 : ℕ) : ℝ) / (m : ℝ) else 0) *
      (if r₁ < m then -(((k₁ + s : ℕ) : ℝ) + ((r₁ + 1 : ℕ) : ℝ) / (m : ℝ))
        else -((k₁ + 1 : ℕ) : ℝ)) +
      (if r₂ < m then ((k₂ + s : ℕ) : ℝ) + ((r₂ + 1 : ℕ) : ℝ) / (m : ℝ)
        else ((k₂ + 1 : ℕ) : ℝ))
  by_cases hr2 : r₂ < m
  · simp only [hr2, ite_true]
    have hcast_m : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm, Nat.cast_one]
    have hu2_pos : 0 < ((k₂ + s : ℕ) : ℝ) + ((r₂ + 1 : ℕ) : ℝ) / (m : ℝ) := by positivity
    -- Bound `-t(q₁) ≤ u(k₂, r₂ + 1)`.
    have hv_le :
        (if r₁ < m then ((k₁ + s : ℕ) : ℝ) + ((r₁ + 1 : ℕ) : ℝ) / (m : ℝ)
          else ((k₁ + 1 : ℕ) : ℝ)) ≤
        ((k₂ + s : ℕ) : ℝ) + ((r₂ + 1 : ℕ) : ℝ) / (m : ℝ) := by
      split_ifs with hr1
      · rcases eq_or_lt_of_le hk_le with hkeq | hklt
        · have hrle : r₁ ≤ r₂ := by
            have : (m + 1) * k₁ + r₁ ≤ (m + 1) * k₂ + r₂ := by omega
            rw [hkeq] at this
            omega
          rw [hkeq]
          gcongr
        · have hrm : ((r₁ + 1 : ℕ) : ℝ) / (m : ℝ) ≤ 1 := by
            rw [div_le_one hm_pos]
            exact_mod_cast (by omega : r₁ + 1 ≤ m)
          have hkk : ((k₁ + s : ℕ) : ℝ) + 1 ≤ ((k₂ + s : ℕ) : ℝ) := by
            have : k₁ + s + 1 ≤ k₂ + s := by omega
            exact_mod_cast this
          have hr2_nn : (0 : ℝ) ≤ ((r₂ + 1 : ℕ) : ℝ) / (m : ℝ) := by positivity
          linarith
      · have hklt : k₁ < k₂ := by
          have hr1_eq : r₁ = m := by omega
          by_contra h
          have hkeq : k₁ = k₂ := by omega
          have : (m + 1) * k₁ + r₁ ≤ (m + 1) * k₂ + r₂ := by omega
          rw [hkeq, hr1_eq] at this
          omega
        have hkk : ((k₁ + 1 : ℕ) : ℝ) ≤ ((k₂ + s : ℕ) : ℝ) := by
          have : k₁ + 1 ≤ k₂ + s := by omega
          exact_mod_cast this
        have hr2_nn : (0 : ℝ) ≤ ((r₂ + 1 : ℕ) : ℝ) / (m : ℝ) := by positivity
        linarith
    have hneg :
        (if r₁ < m then -(((k₁ + s : ℕ) : ℝ) + ((r₁ + 1 : ℕ) : ℝ) / (m : ℝ))
          else -((k₁ + 1 : ℕ) : ℝ)) =
        -(if r₁ < m then ((k₁ + s : ℕ) : ℝ) + ((r₁ + 1 : ℕ) : ℝ) / (m : ℝ)
          else ((k₁ + 1 : ℕ) : ℝ)) := by
      split_ifs <;> rfl
    rw [hneg, hcast_m]
    have ha_nn : 0 ≤ ((m : ℝ) - 1) / (m : ℝ) := by
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      exact div_nonneg (by linarith) hm_pos.le
    have hbound :
        (((m : ℝ) - 1) / (m : ℝ)) *
          (if r₁ < m then ((k₁ + s : ℕ) : ℝ) + ((r₁ + 1 : ℕ) : ℝ) / (m : ℝ)
            else ((k₁ + 1 : ℕ) : ℝ)) ≤
        (((m : ℝ) - 1) / (m : ℝ)) * (((k₂ + s : ℕ) : ℝ) + ((r₂ + 1 : ℕ) : ℝ) / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hv_le ha_nn
    have hgap :
        (((k₂ + s : ℕ) : ℝ) + ((r₂ + 1 : ℕ) : ℝ) / (m : ℝ)) -
          (((m : ℝ) - 1) / (m : ℝ)) * (((k₂ + s : ℕ) : ℝ) + ((r₂ + 1 : ℕ) : ℝ) / (m : ℝ)) =
        (((k₂ + s : ℕ) : ℝ) + ((r₂ + 1 : ℕ) : ℝ) / (m : ℝ)) / (m : ℝ) := by
      field_simp [hm_pos.ne']
      ring
    have hgap_pos : 0 < (((k₂ + s : ℕ) : ℝ) + ((r₂ + 1 : ℕ) : ℝ) / (m : ℝ)) / (m : ℝ) :=
      div_pos hu2_pos hm_pos
    linarith
  · simp only [hr2, ite_false, zero_mul, zero_add]
    positivity

private theorem ratProd_sq_group {m : ℕ} (hm : 1 ≤ m) (s n k : ℕ) :
    ratProd (sqT m s) (sqA m) (sqB m s) (k * (m + 1)) (n : ℝ) =
      squareUnified m s n k / squareUnified m s n 0 := by
  induction k with
  | zero =>
    have h0 : squareUnified m s n 0 ≠ 0 := (squareUnified_pos hm s n 0).ne'
    simp [div_self h0]
  | succ k ih =>
    rw [show (k + 1) * (m + 1) = k * (m + 1) + (m + 1) by ring, ratProd_add, ih]
    have hblock :
        ratProd (fun h => sqT m s (k * (m + 1) + h))
          (fun h => sqA m (k * (m + 1) + h))
          (fun h => sqB m s (k * (m + 1) + h)) (m + 1) (n : ℝ) =
        squareUnified m s n (k + 1) / squareUnified m s n k := by
      rw [squareUnified_succ_col hm s n k, ratProd_succ]
      congr 1
      · unfold ratProd
        refine Finset.prod_congr rfl fun r hr => ?_
        have hrm : r < m := Finset.mem_range.mp hr
        have hdiv : (k * (m + 1) + r) / (m + 1) = k := by
          rw [mul_comm, Nat.mul_add_div (by omega : 0 < m + 1), Nat.div_eq_of_lt (by omega : r < m + 1), add_zero]
        have hmod : (k * (m + 1) + r) % (m + 1) = r := by
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega : r < m + 1)]
        simp only [sqT, sqA, sqB, hdiv, hmod, hrm, ite_true, sub_neg_eq_add]
        ring
      · have hdiv : (k * (m + 1) + m) / (m + 1) = k := by
          rw [mul_comm, Nat.mul_add_div (by omega : 0 < m + 1), Nat.div_eq_of_lt (by omega : m < m + 1), add_zero]
        have hmod : (k * (m + 1) + m) % (m + 1) = m := by
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega : m < m + 1)]
        simp only [sqT, sqA, sqB, hdiv, hmod, lt_irrefl, ite_false, zero_mul, zero_add,
          sub_neg_eq_add]
    rw [hblock]
    have hk : squareUnified m s n k ≠ 0 := (squareUnified_pos hm s n k).ne'
    have h0 : squareUnified m s n 0 ≠ 0 := (squareUnified_pos hm s n 0).ne'
    field_simp [hk, h0]

/-- Unified square matrix `S_s(n, k)` is strictly totally positive for every `m ≥ 1`. -/
theorem squareUnified_isStrictlyTotallyPos {m : ℕ} (hm : 1 ≤ m) (s : ℕ) :
    IsStrictlyTotallyPos (fun n k : ℕ => squareUnified m s n k) := by
  let E : Matrix ℕ ℕ ℝ := fun n q => ratProd (sqT m s) (sqA m) (sqB m s) q (n : ℝ)
  have hE : IsStrictlyTotallyPos E := by
    apply isStrictlyTotallyPos_of_consecutive_cols
    intro p rows start hrows
    apply det_ratProd_pos (sqT m s) (sqA m) (sqB m s) start p (fun i => (rows i : ℝ))
    · intro a b hab
      exact Nat.cast_lt.mpr (hrows hab)
    · intro i h _
      exact sq_den_pos_nonneg hm s h (Nat.cast_nonneg _)
    · intro i
      unfold ratProd
      refine Finset.prod_pos fun h _ => div_pos ?_ (sq_den_pos_nonneg hm s h (Nat.cast_nonneg _))
      have hneg := sqT_neg hm s h
      have hnn : (0 : ℝ) ≤ (rows i : ℝ) := Nat.cast_nonneg _
      linarith
    · intro r q _ hrq _
      exact sq_cross_pos hm s r q hrq
  have hsub : IsStrictlyTotallyPos (E.submatrix id (fun k => k * (m + 1))) :=
    hE.submatrix strictMono_id (fun a b hab =>
      Nat.mul_lt_mul_of_pos_right hab (by omega))
  exact hsub.of_row_col_scale
    (r := fun n => squareUnified m s n 0) (c := fun _ => 1)
    (fun n => squareUnified_pos hm s n 0) (fun _ => zero_lt_one)
    (fun n k => by
      change squareUnified m s n k =
        squareUnified m s n 0 * ratProd (sqT m s) (sqA m) (sqB m s) (k * (m + 1)) (n : ℝ) * 1
      rw [mul_one, ratProd_sq_group hm s n k, mul_div_cancel₀ _ (squareUnified_pos hm s n 0).ne'])

/-- **Wang–Yang Conjecture 4.1 (Type B square)**: `[B(n + k, k)]` is strictly totally positive
for every integer `m ≥ 2`. -/
theorem matBSquare_isStrictlyTotallyPos {m : ℕ} (hm : 2 ≤ m) :
    IsStrictlyTotallyPos (matBSquare m) := by
  have heq : matBSquare m = (fun n k => squareUnified m 0 n k) := by
    ext n k
    exact matBSquare_eq_squareUnified m n k
  rw [heq]
  exact squareUnified_isStrictlyTotallyPos (by omega : 1 ≤ m) 0

/-- **Wang–Yang Conjecture 4.1 (Type A square)**: `[A(n + k, k)]` is strictly totally positive
for every integer `m ≥ 2`. -/
theorem matASquare_isStrictlyTotallyPos {m : ℕ} (hm : 2 ≤ m) :
    IsStrictlyTotallyPos (matASquare m) := by
  exact (squareUnified_isStrictlyTotallyPos (by omega : 1 ≤ m) 1).of_row_col_scale
    (r := fun n => (((n + 1 : ℕ) : ℝ))⁻¹) (c := fun _ => 1)
    (fun n => by positivity) (fun _ => zero_lt_one)
    (fun n k => by
      rw [matASquare_eq_squareUnified]
      ring)

end Squares

/-! ### Part 2: The two ordinary triangles are totally nonnegative -/

section OrdinaryTriangles

private noncomputable def ordBase (s h : ℕ) : ℝ :=
  if h % 2 = 0 then ((h / 2 : ℕ) : ℝ) - (s : ℝ) else ((h / 2 : ℕ) : ℝ)

private noncomputable def ordA (m h : ℕ) : ℝ :=
  if h % 2 = 0 then 0 else ((m - 1 : ℕ) : ℝ)

private noncomputable def ordB (m s h : ℕ) : ℝ :=
  if h % 2 = 0 then 1 else (m : ℝ) * (s : ℝ) + ((h / 2 : ℕ) : ℝ) + 1

private theorem ordBase_mono {s : ℕ} (hs : s ≤ 1) : Monotone (ordBase s) := by
  intro i j hij
  unfold ordBase
  split_ifs with hi hj
  · have : i / 2 ≤ j / 2 := Nat.div_le_div_right hij
    have : ((i / 2 : ℕ) : ℝ) ≤ ((j / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  · have : i / 2 ≤ j / 2 := Nat.div_le_div_right hij
    have : ((i / 2 : ℕ) : ℝ) ≤ ((j / 2 : ℕ) : ℝ) := by exact_mod_cast this
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    linarith
  · have hlt : i < j := by omega
    have hdiv : i / 2 + 1 ≤ j / 2 := by omega
    have hdivR : ((i / 2 : ℕ) : ℝ) + 1 ≤ ((j / 2 : ℕ) : ℝ) := by exact_mod_cast hdiv
    have hs1 : (s : ℝ) ≤ 1 := by exact_mod_cast hs
    linarith
  · have : i / 2 ≤ j / 2 := Nat.div_le_div_right hij
    exact_mod_cast this

private theorem ordBase_ge_neg_s (s h : ℕ) : -(s : ℝ) ≤ ordBase s h := by
  unfold ordBase
  split_ifs <;> linarith [Nat.cast_nonneg (α := ℝ) (h / 2), Nat.cast_nonneg (α := ℝ) s]

private theorem ord_den_ge_one {m : ℕ} (hm : 1 ≤ m) (s h : ℕ) {x : ℝ} (hx : -(s : ℝ) ≤ x) :
    1 ≤ ordA m h * x + ordB m s h := by
  unfold ordA ordB
  split_ifs
  · linarith
  · have hcast_m : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm, Nat.cast_one]
    have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have h1 : ((m : ℝ) - 1) * (-(s : ℝ)) ≤ ((m : ℝ) - 1) * x :=
      mul_le_mul_of_nonneg_left hx hm1
    have hnn : (0 : ℝ) ≤ (s : ℝ) + ((h / 2 : ℕ) : ℝ) := by positivity
    rw [hcast_m]
    linarith

private theorem ordBase_at_row {s : ℕ} (hs : s ≤ 1) (n : ℕ) :
    ordBase s (2 * n + s) = (n : ℝ) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with rfl | rfl
  · unfold ordBase
    simp
  · unfold ordBase
    have hd : (2 * n + 1) / 2 = n := by omega
    simp [hd]

private theorem ratProd_ord_even (m s n k : ℕ) :
    ratProd (ordBase s) (ordA m) (ordB m s) (2 * k) (n : ℝ) =
      ∏ j ∈ Finset.range k,
        ((((n : ℝ) - (j : ℝ) + (s : ℝ)) * ((n : ℝ) - (j : ℝ))) /
          (((m - 1 : ℕ) : ℝ) * (n : ℝ) + (m : ℝ) * (s : ℝ) + (j : ℝ) + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, ratProd_succ, ratProd_succ, ih,
      Finset.prod_range_succ, mul_assoc]
    congr 1
    have h0m : (2 * k) % 2 = 0 := by omega
    have h0d : (2 * k) / 2 = k := by omega
    have h1m : (2 * k + 1) % 2 ≠ 0 := by omega
    have h1d : (2 * k + 1) / 2 = k := by omega
    simp only [ordBase, ordA, ordB, h0m, h0d, h1m, h1d, ite_true, ite_false, zero_mul, zero_add,
      div_one]
    ring

/-- Unified ordinary triangle `fussEntry m s` is totally nonnegative for `m ≥ 1`, `s ≤ 1`. -/
theorem fussEntry_isTotallyNonneg {m s : ℕ} (hm : 1 ≤ m) (hs : s ≤ 1) :
    Matrix.IsTotallyNonneg (Matrix.of fun n k : ℕ => fussEntry m s n k) := by
  apply isTotallyNonneg_of_fin_sections
  intro N
  let M : ℕ := 2 * N + 2
  let node : ℝ → ℕ → ℝ := fun ε i => ordBase s i + ε * (i : ℝ)
  let L : ℝ → Matrix (Fin M) (Fin M) ℝ := fun ε i j =>
    ratProd (node ε) (ordA m) (ordB m s) j.val (node ε i.val)
  let L0 : Matrix (Fin M) (Fin M) ℝ := fun i j =>
    ratProd (ordBase s) (ordA m) (ordB m s) j.val (ordBase s i.val)
  -- Step 1: For every `ε > 0`, `L ε` is TN by the triangular minor test + Formula (1).
  have hL_TN : ∀ ε : ℝ, 0 < ε → (L ε).IsTotallyNonneg := by
    intro ε hε
    have hnode_strict : StrictMono (node ε) := by
      intro i j hij
      have h1 : ordBase s i ≤ ordBase s j := ordBase_mono hs hij.le
      have h2 : ε * (i : ℝ) < ε * (j : ℝ) :=
        mul_lt_mul_of_pos_left (by exact_mod_cast hij) hε
      dsimp only [node]
      linarith
    have hnode_ge : ∀ i : ℕ, -(s : ℝ) ≤ node ε i := fun i => by
      have h1 := ordBase_ge_neg_s s i
      have h2 : 0 ≤ ε * (i : ℝ) := by positivity
      dsimp only [node]
      linarith
    apply isTotallyNonneg_of_lowerTriangular_flag_pos M (L ε)
    · intro i j hij
      have hij' : i.val < j.val := hij
      dsimp only [L, ratProd]
      refine Finset.prod_eq_zero (Finset.mem_range.mpr hij') ?_
      simp
    · intro k start hsk
      have hdet := det_ratProd_pos (node ε) (ordA m) (ordB m s) 0 k
        (fun i : Fin k => node ε (start + i.val))
        (fun a b hab => hnode_strict (by omega))
        (fun i h _ => lt_of_lt_of_le zero_lt_one (ord_den_ge_one hm s h (hnode_ge _)))
        (fun i => by simp)
        (fun r q _ _ _ => lt_of_lt_of_le zero_lt_one (ord_den_ge_one hm s q (hnode_ge _)))
      simpa [L] using hdet
  -- Step 2: `L ε → L0` as `ε → 0⁺`, so `L0` is TN.
  have hlim : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 L0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    dsimp only [L, L0, ratProd]
    refine tendsto_finsetProd (Finset.range j.val) fun h _ => ?_
    have hnode_lim : ∀ r : ℕ, Tendsto (fun ε : ℝ => node ε r) (𝓝[>] (0 : ℝ)) (𝓝 (ordBase s r)) := by
      intro r
      have hmul : Tendsto (fun ε : ℝ => ε * (r : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 * (r : ℝ))) :=
        (continuousWithinAt_id).mul tendsto_const_nhds
      simpa [node] using tendsto_const_nhds.add hmul
    have hnum : Tendsto (fun ε : ℝ => node ε i.val - node ε h) (𝓝[>] (0 : ℝ))
        (𝓝 (ordBase s i.val - ordBase s h)) :=
      (hnode_lim i.val).sub (hnode_lim h)
    have hden : Tendsto (fun ε : ℝ => ordA m h * node ε i.val + ordB m s h) (𝓝[>] (0 : ℝ))
        (𝓝 (ordA m h * ordBase s i.val + ordB m s h)) :=
      (tendsto_const_nhds.mul (hnode_lim i.val)).add tendsto_const_nhds
    have hne : ordA m h * ordBase s i.val + ordB m s h ≠ 0 :=
      (lt_of_lt_of_le zero_lt_one (ord_den_ge_one hm s h (ordBase_ge_neg_s s i.val))).ne'
    exact hnum.div hden hne
  have hL0_TN : L0.IsTotallyNonneg :=
    isTotallyNonneg_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => hL_TN ε hε)
  -- Step 3: Extract the `(2n + s, 2k)` submatrix and restore positive scalings.
  let rowMap : Fin N → Fin M := fun n => ⟨2 * n.val + s, by omega⟩
  let colMap : Fin N → Fin M := fun k => ⟨2 * k.val, by omega⟩
  have hrow_mono : StrictMono rowMap := fun a b hab => by
    change 2 * a.val + s < 2 * b.val + s
    omega
  have hcol_mono : StrictMono colMap := fun a b hab => by
    change 2 * a.val < 2 * b.val
    omega
  have hsub_TN : (L0.submatrix rowMap colMap).IsTotallyNonneg :=
    hL0_TN.submatrix hrow_mono hcol_mono
  exact isTotallyNonneg_of_row_col_scale hsub_TN
    (r := fun n : Fin N => fussEntry m s n.val 0)
    (c := fun k : Fin N => ((k.val.factorial : ℝ))⁻¹)
    (fun n => (fussEntry_col_zero_pos hm s n.val).le)
    (fun k => by positivity)
    (fun n k => by
      change fussEntry m s n.val k.val =
        fussEntry m s n.val 0 *
          ratProd (ordBase s) (ordA m) (ordB m s) (2 * k.val) (ordBase s (2 * n.val + s)) *
          ((k.val.factorial : ℝ))⁻¹
      rw [ordBase_at_row hs n.val, ratProd_ord_even]
      have hid := ordinary_product_identity hm s n.val k.val
      have hfac : (k.val.factorial : ℝ) ≠ 0 := by positivity
      calc
        fussEntry m s n.val k.val
            = (k.val.factorial : ℝ) * fussEntry m s n.val k.val * ((k.val.factorial : ℝ))⁻¹ := by
                field_simp [hfac]
        _ = fussEntry m s n.val 0 *
              (∏ j ∈ Finset.range k.val,
                ((((n.val : ℝ) - (j : ℝ) + (s : ℝ)) * ((n.val : ℝ) - (j : ℝ))) /
                  (((m - 1 : ℕ) : ℝ) * (n.val : ℝ) + (m : ℝ) * (s : ℝ) + (j : ℝ) + 1))) *
              ((k.val.factorial : ℝ))⁻¹ := by rw [hid])

/-- **Wang–Yang Conjecture 4.1 (Ordinary Type B triangle)**: `[B(n, k)]` is totally nonnegative
for every integer `m ≥ 2`. -/
theorem matB_isTotallyNonneg {m : ℕ} (hm : 2 ≤ m) :
    (matB m).IsTotallyNonneg := by
  have heq : matB m = Matrix.of (fun n k => fussEntry m 0 n k) := by
    ext n k
    exact (fussEntry_zero m n k).symm
  rw [heq]
  exact fussEntry_isTotallyNonneg (by omega : 1 ≤ m) (by omega : 0 ≤ 1)

/-- **Wang–Yang Conjecture 4.1 (Ordinary Type A triangle)**: `[A(n, k)]` is totally nonnegative
for every integer `m ≥ 2`. -/
theorem matA_isTotallyNonneg {m : ℕ} (hm : 2 ≤ m) :
    (matA m).IsTotallyNonneg := by
  have heq : matA m = Matrix.of (fun n k => fussEntry m 1 n k) := by
    ext n k
    exact (fussEntry_one m n k).symm
  rw [heq]
  exact fussEntry_isTotallyNonneg (by omega : 1 ≤ m) (by omega : 1 ≤ 1)

end OrdinaryTriangles

/-! ### Part 3: The two row-reversed triangles are totally nonnegative -/

section ReversedTriangles

private noncomputable def revAlpha (m s h : ℕ) : ℝ :=
  if h % 2 = 0 then ((h / 2 : ℕ) : ℝ) else ((h / 2 : ℕ) : ℝ) / (m : ℝ) - (s : ℝ)

private theorem capValid_revAlpha {m : ℕ} (hm : 1 ≤ m) (s : ℕ) :
    ∀ (N : ℕ) (k : ℕ),
      CapValid N (fun r => revAlpha m s (2 * k + r)) (fun r => ((k + r : ℕ) : ℝ)) ∧
      CapValid N (fun r => revAlpha m s (2 * k + 1 + r)) (fun r => ((k + 1 + r : ℕ) : ℝ))
  | 0, _ => ⟨trivial, trivial⟩
  | N + 1, k => by
    have ih := capValid_revAlpha hm s N
    constructor
    · left
      refine ⟨?_, ?_⟩
      · unfold revAlpha
        simp
      · have h1 : (fun r => revAlpha m s (2 * k + (r + 1))) =
            (fun r => revAlpha m s (2 * k + 1 + r)) := funext fun r => by congr 1; omega
        have h2 : (fun r : ℕ => ((k + (r + 1) : ℕ) : ℝ)) =
            (fun r : ℕ => ((k + 1 + r : ℕ) : ℝ)) := funext fun r => by congr 1; omega
        rw [h1, h2]
        exact (ih k).2
    · right
      refine ⟨?_, ?_⟩
      · unfold revAlpha
        have hm1 : (2 * k + 1 + 0) % 2 ≠ 0 := by omega
        have hd1 : (2 * k + 1 + 0) / 2 = k := by omega
        simp only [hm1, ite_false, hd1, Nat.add_zero]
        have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hdiv : (k : ℝ) / (m : ℝ) ≤ (k : ℝ) := div_le_self (Nat.cast_nonneg k) hmR
        have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
        push_cast
        linarith
      · have h1 : (fun r => revAlpha m s (2 * k + 1 + (r + 1))) =
            (fun r => revAlpha m s (2 * (k + 1) + r)) := funext fun r => by congr 1; omega
        rw [h1]
        exact (ih (k + 1)).1

private theorem fallingMatrix_isTotallyNonneg (M : ℕ) :
    (Matrix.of fun i j : Fin M => newtonBasis (fun r => (r : ℝ)) j.val (i.val : ℝ)).IsTotallyNonneg := by
  apply isTotallyNonneg_of_lowerTriangular_flag_pos M
  · intro i j hij
    have hij' : i.val < j.val := hij
    dsimp only [Matrix.of_apply, newtonBasis]
    refine Finset.prod_eq_zero (Finset.mem_range.mpr hij') ?_
    simp
  · intro k start hsk
    have hdet := det_newtonBasis k (fun r => (r : ℝ))
      (fun i : Fin k => ((start + i.val : ℕ) : ℝ))
    have hpos : 0 < ∏ i : Fin k, ∏ j ∈ Finset.Ioi i,
        (((start + j.val : ℕ) : ℝ) - ((start + i.val : ℕ) : ℝ)) := by
      refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
      have hij : i < j := Finset.mem_Ioi.mp hj
      have hlt : start + i.val < start + j.val := by omega
      have hltR : ((start + i.val : ℕ) : ℝ) < ((start + j.val : ℕ) : ℝ) := by exact_mod_cast hlt
      linarith
    rw [← hdet] at hpos
    exact hpos

private theorem newtonBasis_revAlpha_even (m s n k : ℕ) :
    newtonBasis (revAlpha m s) (2 * k) (n : ℝ) =
      ∏ j ∈ Finset.range k, (((n : ℝ) - (j : ℝ)) * ((n : ℝ) - ((j : ℝ) / (m : ℝ) - (s : ℝ)))) := by
  induction k with
  | zero => simp [newtonBasis]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, newtonBasis_succ, newtonBasis_succ, ih,
      Finset.prod_range_succ, mul_assoc]
    congr 1
    have h0m : (2 * k) % 2 = 0 := by omega
    have h0d : (2 * k) / 2 = k := by omega
    have h1d : (2 * k + 1) / 2 = k := by omega
    simp [revAlpha, h0m, h0d, h1d]

/-- Unified reversed matrix `C(n, k) * C(m * (n + s), k)` is totally nonnegative for `m ≥ 1`. -/
theorem reversedUnified_isTotallyNonneg {m : ℕ} (hm : 1 ≤ m) (s : ℕ) :
    Matrix.IsTotallyNonneg
      (Matrix.of fun n k : ℕ => (Nat.choose n k : ℝ) * (Nat.choose (m * (n + s)) k : ℝ)) := by
  apply isTotallyNonneg_of_fin_sections
  intro N
  let M : ℕ := 2 * N + 1
  let H : Matrix (Fin M) (Fin M) ℝ :=
    Matrix.of fun i j => newtonBasis (fun r => (r : ℝ)) j.val (i.val : ℝ)
  let C : Matrix (Fin M) (Fin M) ℝ := newtonChangeMat M (revAlpha m s) (fun r => (r : ℝ))
  have hH_TN : H.IsTotallyNonneg := fallingMatrix_isTotallyNonneg M
  have hC_TN : C.IsTotallyNonneg := by
    apply newtonChangeMat_isTotallyNonneg M (revAlpha m s) (fun r => (r : ℝ))
    · intro x y hxy; exact Nat.cast_le.mpr hxy
    · have hcap := (capValid_revAlpha hm s M 0).1
      convert hcap using 1 <;> (funext r; simp)
  have hprod_TN : (H * Cᵀ).IsTotallyNonneg := isTotallyNonneg_mul hH_TN hC_TN.transpose
  have hprod_eval : ∀ (i j : Fin M), (H * Cᵀ) i j = newtonBasis (revAlpha m s) j.val (i.val : ℝ) := by
    intro i j
    rw [Matrix.mul_apply]
    have hsum :
        (∑ r : Fin M, H i r * Cᵀ r j) =
          ∑ r ∈ Finset.range (j.val + 1),
            newtonChange (revAlpha m s) (fun u => (u : ℝ)) j.val r *
              newtonBasis (fun u => (u : ℝ)) r (i.val : ℝ) := by
      change (∑ r : Fin M,
          newtonBasis (fun u => (u : ℝ)) r.val (i.val : ℝ) *
            newtonChange (revAlpha m s) (fun u => (u : ℝ)) j.val r.val) = _
      rw [Fin.sum_univ_eq_sum_range (fun r =>
        newtonBasis (fun u => (u : ℝ)) r (i.val : ℝ) *
          newtonChange (revAlpha m s) (fun u => (u : ℝ)) j.val r)]
      rw [← Finset.sum_subset (Finset.range_mono (by omega : j.val + 1 ≤ M))]
      · refine Finset.sum_congr rfl fun r _ => mul_comm _ _
      · intro r _ hnot
        have hgt : j.val < r := by
          have : ¬ r < j.val + 1 := fun h => hnot (Finset.mem_range.mpr h)
          omega
        rw [newtonChange_eq_zero_of_lt _ _ hgt, mul_zero]
    rw [hsum, sum_newtonChange_mul_newtonBasis]
  let rowMap : Fin N → Fin M := fun n => ⟨n.val, by omega⟩
  let colMap : Fin N → Fin M := fun k => ⟨2 * k.val, by omega⟩
  have hrow_mono : StrictMono rowMap := fun a b hab => hab
  have hcol_mono : StrictMono colMap := fun a b hab => by
    change 2 * a.val < 2 * b.val
    omega
  have hsub_TN : ((H * Cᵀ).submatrix rowMap colMap).IsTotallyNonneg :=
    hprod_TN.submatrix hrow_mono hcol_mono
  exact isTotallyNonneg_of_row_col_scale hsub_TN
    (r := fun _ : Fin N => (1 : ℝ))
    (c := fun k : Fin N => (m : ℝ) ^ k.val / ((k.val.factorial : ℝ) ^ 2))
    (fun _ => zero_le_one)
    (fun k => by positivity)
    (fun n k => by
      change (Nat.choose n.val k.val : ℝ) * (Nat.choose (m * (n.val + s)) k.val : ℝ) =
        1 * (H * Cᵀ) (rowMap n) (colMap k) * ((m : ℝ) ^ k.val / ((k.val.factorial : ℝ) ^ 2))
      rw [one_mul, hprod_eval]
      simp only [rowMap, colMap, newtonBasis_revAlpha_even, reversed_product_identity hm s n.val k.val]
      have hm_ne : (m : ℝ) ^ k.val ≠ 0 := by positivity
      have hfac_ne : (k.val.factorial : ℝ) ^ 2 ≠ 0 := by positivity
      field_simp [hm_ne, hfac_ne])

/-- **Wang–Yang Conjecture 4.1 (Reversed Type B triangle)**: `[B(n, n - k)]` is totally
nonnegative for every integer `m ≥ 2`. -/
theorem matBRev_isTotallyNonneg {m : ℕ} (hm : 2 ≤ m) :
    (matBRev m).IsTotallyNonneg := by
  have heq : matBRev m =
      Matrix.of (fun n k => (Nat.choose n k : ℝ) * (Nat.choose (m * (n + 0)) k : ℝ)) := by
    ext n k
    simp [matBRev_eq]
  rw [heq]
  exact reversedUnified_isTotallyNonneg (by omega : 1 ≤ m) 0

/-- **Wang–Yang Conjecture 4.1 (Reversed Type A triangle)**: `[A(n, n - k)]` is totally
nonnegative for every integer `m ≥ 2`. -/
theorem matARev_isTotallyNonneg {m : ℕ} (hm : 2 ≤ m) :
    (matARev m).IsTotallyNonneg := by
  exact isTotallyNonneg_of_row_col_scale (reversedUnified_isTotallyNonneg (by omega : 1 ≤ m) 1)
    (r := fun _ => (1 : ℝ))
    (c := fun k => (((k + 1 : ℕ) : ℝ))⁻¹)
    (fun _ => zero_le_one)
    (fun k => by positivity)
    (fun n k => by
      rw [matARev_eq]
      simp only [Matrix.of_apply]
      ring)

end ReversedTriangles

/-! ### Combined statement of Wang–Yang Conjecture 4.1 -/

/-- **Wang–Yang Conjecture 4.1**: for every integer `m ≥ 2`, the four Fuss–Narayana triangles
`A(n, k)`, `B(n, k)`, `A(n, n - k)`, `B(n, n - k)` are totally nonnegative and the two
Fuss–Narayana squares `A(n + k, k)`, `B(n + k, k)` are strictly totally positive. -/
theorem wang_yang_fuss_narayana_conjecture {m : ℕ} (hm : 2 ≤ m) :
    (matB m).IsTotallyNonneg ∧
    (matA m).IsTotallyNonneg ∧
    (matBRev m).IsTotallyNonneg ∧
    (matARev m).IsTotallyNonneg ∧
    IsStrictlyTotallyPos (matBSquare m) ∧
    IsStrictlyTotallyPos (matASquare m) :=
  ⟨matB_isTotallyNonneg hm,
   matA_isTotallyNonneg hm,
   matBRev_isTotallyNonneg hm,
   matARev_isTotallyNonneg hm,
   matBSquare_isStrictlyTotallyPos hm,
   matASquare_isStrictlyTotallyPos hm⟩

end Conjectures.WangYangFussNarayana
