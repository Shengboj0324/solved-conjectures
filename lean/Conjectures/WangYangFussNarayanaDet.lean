import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Krattenthaler's Product Determinant (Lemma 3)

Proves the polynomial and rational-product determinant identities (Formula (1) in `proof.md`)
via two triangular factorizations and `Matrix.det_vandermonde`:
- Polynomial form (over any commutative ring, no nonvanishing or distinctness assumptions):
  for `Q_j(x) = (∏_{h < j} (x - t_h)) * (∏_{j ≤ h < d} (a_h * x + b_h))`,
  `det [Q_j(x_i)]_{i, j : Fin (d + 1)} = (∏_{i < j} (x_j - x_i)) * (∏_{0 ≤ i ≤ j < d} (a_j * t_i + b_j))`.
- Rational form starting at any column `start` and positivity corollary.
-/

namespace Conjectures.WangYangFussNarayana

open Matrix Finset Polynomial
open scoped BigOperators

/-- Newton basis polynomial `∏_{h < k} (x - t_h)`. -/
def newtonBasis {R : Type*} [CommRing R] (t : ℕ → R) (k : ℕ) (x : R) : R :=
  ∏ h ∈ Finset.range k, (x - t h)

theorem newtonBasis_zero {R : Type*} [CommRing R] (t : ℕ → R) (x : R) :
    newtonBasis t 0 x = 1 := by
  simp [newtonBasis]

theorem newtonBasis_succ {R : Type*} [CommRing R] (t : ℕ → R) (k : ℕ) (x : R) :
    newtonBasis t (k + 1) x = newtonBasis t k x * (x - t k) := by
  simp [newtonBasis, Finset.prod_range_succ]

/-- Coefficients expanding `newtonBasis t j x * ∏_{s < r} (a (j + s) * x + b (j + s))`
in the Newton basis `{newtonBasis t k x}`. -/
def affineExpand {R : Type*} [CommRing R] (t a b : ℕ → R) (j : ℕ) : ℕ → ℕ → R
  | 0, k => if k = j then 1 else 0
  | r + 1, k =>
      (a (j + r) * t k + b (j + r)) * affineExpand t a b j r k +
        if k = 0 then 0 else a (j + r) * affineExpand t a b j r (k - 1)

theorem affineExpand_eq_zero_of_lt {R : Type*} [CommRing R] (t a b : ℕ → R) (j r k : ℕ)
    (hk : k < j) : affineExpand t a b j r k = 0 := by
  induction r generalizing k with
  | zero =>
    simp [affineExpand, ne_of_lt hk]
  | succ r ih =>
    simp only [affineExpand, ih k hk, mul_zero, zero_add]
    split_ifs with hk0
    · rfl
    · rw [ih (k - 1) (by omega), mul_zero]

theorem affineExpand_eq_zero_of_gt {R : Type*} [CommRing R] (t a b : ℕ → R) (j r k : ℕ)
    (hk : j + r < k) : affineExpand t a b j r k = 0 := by
  induction r generalizing k with
  | zero =>
    simp only [Nat.add_zero] at hk
    simp [affineExpand, ne_of_gt hk]
  | succ r ih =>
    simp only [affineExpand, ih k (by omega), mul_zero, zero_add]
    split_ifs with hk0
    · rfl
    · rw [ih (k - 1) (by omega), mul_zero]

theorem affineExpand_diag {R : Type*} [CommRing R] (t a b : ℕ → R) (j r : ℕ) :
    affineExpand t a b j r j = ∏ s ∈ Finset.range r, (a (j + s) * t j + b (j + s)) := by
  induction r with
  | zero => simp [affineExpand]
  | succ r ih =>
    rw [Finset.prod_range_succ, ← ih]
    simp only [affineExpand]
    have hprev : (if j = 0 then (0 : R) else a (j + r) * affineExpand t a b j r (j - 1)) = 0 := by
      split_ifs with hj0
      · rfl
      · rw [affineExpand_eq_zero_of_lt t a b j r (j - 1) (by omega), mul_zero]
    rw [hprev, add_zero, mul_comm]

theorem sum_affineExpand_mul_newtonBasis {R : Type*} [CommRing R]
    (t a b : ℕ → R) (j r : ℕ) (x : R) :
    (∑ k ∈ Finset.range (j + r + 1), affineExpand t a b j r k * newtonBasis t k x) =
      newtonBasis t j x * ∏ s ∈ Finset.range r, (a (j + s) * x + b (j + s)) := by
  induction r with
  | zero =>
    rw [Finset.prod_range_zero, mul_one, Nat.add_zero]
    rw [Finset.sum_eq_single j]
    · simp [affineExpand]
    · intro k _ hkj
      simp [affineExpand, hkj]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self j)) h
  | succ r ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih, Finset.sum_mul]
    have hsplit : ∀ k,
        affineExpand t a b j r k * newtonBasis t k x * (a (j + r) * x + b (j + r)) =
          (a (j + r) * t k + b (j + r)) * affineExpand t a b j r k * newtonBasis t k x +
            a (j + r) * affineExpand t a b j r k * newtonBasis t (k + 1) x := by
      intro k
      rw [newtonBasis_succ]
      ring
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hfirst :
        (∑ k ∈ Finset.range (j + r + 1),
          (a (j + r) * t k + b (j + r)) * affineExpand t a b j r k * newtonBasis t k x) =
        ∑ k ∈ Finset.range (j + (r + 1) + 1),
          (a (j + r) * t k + b (j + r)) * affineExpand t a b j r k * newtonBasis t k x := by
      symm
      rw [show j + (r + 1) + 1 = (j + r + 1) + 1 by omega, Finset.sum_range_succ,
        affineExpand_eq_zero_of_gt t a b j r (j + r + 1) (by omega)]
      simp
    have hsecond :
        (∑ k ∈ Finset.range (j + r + 1),
          a (j + r) * affineExpand t a b j r k * newtonBasis t (k + 1) x) =
        ∑ k ∈ Finset.range (j + (r + 1) + 1),
          (if k = 0 then (0 : R) else a (j + r) * affineExpand t a b j r (k - 1)) *
            newtonBasis t k x := by
      symm
      rw [show j + (r + 1) + 1 = (j + r + 1) + 1 by omega, Finset.sum_range_succ']
      simp
    rw [hfirst, hsecond, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [affineExpand, add_mul]

/-- The determinant of the Newton-basis evaluation matrix equals the Vandermonde determinant. -/
theorem det_newtonBasis {R : Type*} [CommRing R] (n : ℕ) (t : ℕ → R) (x : Fin n → R) :
    (Matrix.of fun i j : Fin n => newtonBasis t j.val (x i)).det =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i) := by
  nontriviality R
  let p : Fin n → R[X] := fun j => ∏ h ∈ Finset.range j.val, (Polynomial.X - Polynomial.C (t h))
  have hmonic : ∀ j : Fin n, (p j).Monic := fun j =>
    Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _
  have hdeg : ∀ j : Fin n, (p j).natDegree = j.val := by
    intro j
    dsimp [p]
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)]
    simp
  have heval : (Matrix.of fun i j : Fin n => newtonBasis t j.val (x i)) =
      Matrix.of (fun i j : Fin n => (p j).eval (x i)) := by
    ext i j
    simp [p, newtonBasis, Polynomial.eval_prod]
  rw [heval, ← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x p hdeg hmonic,
    Matrix.det_vandermonde]

/-- Polynomial product determinant (Krattenthaler, Lemma 3):
for `Q_j(x) = (∏_{h < j} (x - t_h)) * (∏_{j ≤ h < d} (a_h * x + b_h))`,
`det [Q_j(x_i)]_{0 ≤ i, j ≤ d} = (∏_{i < j} (x_j - x_i)) * (∏_{0 ≤ i ≤ j < d} (a_j * t_i + b_j))`. -/
theorem det_polyProduct {R : Type*} [CommRing R] (d : ℕ) (t a b : ℕ → R)
    (x : Fin (d + 1) → R) :
    (Matrix.of fun i j : Fin (d + 1) =>
        newtonBasis t j.val (x i) *
          ∏ h ∈ Finset.Ico j.val d, (a h * x i + b h)).det =
      (∏ i : Fin (d + 1), ∏ j ∈ Finset.Ioi i, (x j - x i)) *
        ∏ j : Fin d, ∏ h ∈ Finset.Ico j.val d, (a h * t j.val + b h) := by
  let N : Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
    Matrix.of fun i k => newtonBasis t k.val (x i)
  let U : Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
    Matrix.of fun k j => affineExpand t a b j.val (d - j.val) k.val
  have hNU :
      (Matrix.of fun i j : Fin (d + 1) =>
          newtonBasis t j.val (x i) *
            ∏ h ∈ Finset.Ico j.val d, (a h * x i + b h)) = N * U := by
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply]
    have hsum :
        (∑ k : Fin (d + 1), N i k * U k j) =
          ∑ k ∈ Finset.range (j.val + (d - j.val) + 1),
            affineExpand t a b j.val (d - j.val) k * newtonBasis t k (x i) := by
      rw [show j.val + (d - j.val) + 1 = d + 1 by omega, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [N, U, mul_comm]
    rw [hsum, sum_affineExpand_mul_newtonBasis]
    congr 1
    rw [Finset.prod_Ico_eq_prod_range]
  have hlower : U.IsLowerTriangular := by
    intro k j hkj
    exact affineExpand_eq_zero_of_lt t a b j.val (d - j.val) k.val hkj
  rw [hNU, Matrix.det_mul, det_newtonBasis, Matrix.det_of_isLowerTriangular U hlower]
  congr 1
  rw [Fin.prod_univ_castSucc]
  have hlast : U (Fin.last d) (Fin.last d) = 1 := by
    simp [U, affineExpand]
  rw [hlast, mul_one]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [U, Matrix.of_apply, Fin.val_castSucc, affineExpand_diag]
  rw [Finset.prod_Ico_eq_prod_range]

/-- Rational product sequence `F_j(x) = ∏_{h < j} (x - t_h) / (a_h * x + b_h)`. -/
noncomputable def ratProd (t a b : ℕ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  ∏ h ∈ Finset.range j, (x - t h) / (a h * x + b h)

@[simp] theorem ratProd_zero (t a b : ℕ → ℝ) (x : ℝ) : ratProd t a b 0 x = 1 := by
  simp [ratProd]

theorem ratProd_succ (t a b : ℕ → ℝ) (j : ℕ) (x : ℝ) :
    ratProd t a b (j + 1) x = ratProd t a b j x * ((x - t j) / (a j * x + b j)) := by
  unfold ratProd
  exact Finset.prod_range_succ _ j

theorem ratProd_add (t a b : ℕ → ℝ) (start j : ℕ) (x : ℝ) :
    ratProd t a b (start + j) x =
      ratProd t a b start x * ratProd (fun h => t (start + h))
        (fun h => a (start + h)) (fun h => b (start + h)) j x := by
  induction j with
  | zero => simp [ratProd]
  | succ j ih =>
    rw [← Nat.add_assoc, ratProd_succ, ih, ratProd_succ, mul_assoc]

/-- Strict positivity of every consecutive-column minor of `ratProd` (Formula (1) in `proof.md`). -/
theorem det_ratProd_pos (t a b : ℕ → ℝ) (start p : ℕ) (x : Fin p → ℝ)
    (hx : StrictMono x)
    (hden : ∀ (i : Fin p) (h : ℕ), h < start + (p - 1) → 0 < a h * x i + b h)
    (hstart : ∀ i : Fin p, 0 < ratProd t a b start (x i))
    (hcross : ∀ r s : ℕ, start ≤ r → r ≤ s → s < start + (p - 1) → 0 < a s * t r + b s) :
    0 < (Matrix.of fun i j : Fin p => ratProd t a b (start + j.val) (x i)).det := by
  cases p with
  | zero => simp
  | succ d =>
    let t' : ℕ → ℝ := fun h => t (start + h)
    let a' : ℕ → ℝ := fun h => a (start + h)
    let b' : ℕ → ℝ := fun h => b (start + h)
    let w : Fin (d + 1) → ℝ := fun i =>
      ratProd t a b start (x i) / ∏ h ∈ Finset.range d, (a' h * x i + b' h)
    let Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
      Matrix.of fun i j =>
        newtonBasis t' j.val (x i) * ∏ h ∈ Finset.Ico j.val d, (a' h * x i + b' h)
    have hden' : ∀ (i : Fin (d + 1)) (h : ℕ), h < d → 0 < a' h * x i + b' h := by
      intro i h hh
      exact hden i (start + h) (by omega)
    have hw_pos : ∀ i : Fin (d + 1), 0 < w i := by
      intro i
      exact div_pos (hstart i) (Finset.prod_pos fun h hh => hden' i h (Finset.mem_range.mp hh))
    have hmat :
        (Matrix.of fun i j : Fin (d + 1) => ratProd t a b (start + j.val) (x i)) =
          Matrix.diagonal w * Q := by
      ext i j
      rw [Matrix.diagonal_mul, Matrix.of_apply, ratProd_add]
      dsimp only [w, Q, Matrix.of_apply, ratProd, newtonBasis]
      have hsplit_den :
          (∏ h ∈ Finset.range d, (a' h * x i + b' h)) =
            (∏ h ∈ Finset.range j.val, (a' h * x i + b' h)) *
              (∏ h ∈ Finset.Ico j.val d, (a' h * x i + b' h)) := by
        rw [← Nat.Ico_zero_eq_range d, ← Nat.Ico_zero_eq_range j.val]
        exact (Finset.prod_Ico_consecutive (f := fun h => a' h * x i + b' h)
          (Nat.zero_le j.val) (Nat.le_of_lt_succ j.isLt)).symm
      have hd1 : (∏ h ∈ Finset.range j.val, (a' h * x i + b' h)) ≠ 0 :=
        (Finset.prod_pos fun h hh => hden' i h (by
          have := Finset.mem_range.mp hh
          omega)).ne'
      have hd2 : (∏ h ∈ Finset.Ico j.val d, (a' h * x i + b' h)) ≠ 0 :=
        (Finset.prod_pos fun h hh => hden' i h (Finset.mem_Ico.mp hh).2).ne'
      have hprod_div :
          (∏ h ∈ Finset.range j.val, (x i - t' h) / (a' h * x i + b' h)) =
            (∏ h ∈ Finset.range j.val, (x i - t' h)) /
              (∏ h ∈ Finset.range j.val, (a' h * x i + b' h)) :=
        Finset.prod_div_distrib _ _
      change (∏ h ∈ Finset.range start, (x i - t h) / (a h * x i + b h)) *
          (∏ h ∈ Finset.range j.val, (x i - t' h) / (a' h * x i + b' h)) =
        ((∏ h ∈ Finset.range start, (x i - t h) / (a h * x i + b h)) /
          (∏ h ∈ Finset.range d, (a' h * x i + b' h))) *
          ((∏ h ∈ Finset.range j.val, (x i - t' h)) *
            (∏ h ∈ Finset.Ico j.val d, (a' h * x i + b' h)))
      rw [hprod_div, hsplit_den, div_mul_eq_mul_div, ← mul_assoc, mul_div_mul_right _ _ hd2,
        mul_div_assoc']
    rw [hmat, Matrix.det_mul, Matrix.det_diagonal, det_polyProduct]
    have h1 : 0 < ∏ i : Fin (d + 1), w i := Finset.prod_pos fun i _ => hw_pos i
    have h2 : 0 < ∏ i : Fin (d + 1), ∏ j ∈ Finset.Ioi i, (x j - x i) := by
      refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
      exact sub_pos.mpr (hx (Finset.mem_Ioi.mp hj))
    have h3 : 0 < ∏ j : Fin d, ∏ h ∈ Finset.Ico j.val d, (a' h * t' j.val + b' h) := by
      refine Finset.prod_pos fun j _ => Finset.prod_pos fun h hh => ?_
      have hh' := Finset.mem_Ico.mp hh
      exact hcross (start + j.val) (start + h) (by omega) (by omega) (by omega)
    exact mul_pos h1 (mul_pos h2 h3)

end Conjectures.WangYangFussNarayana
