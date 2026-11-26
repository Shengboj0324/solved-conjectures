import Conjectures.WangYangFussNarayanaMatrix
import Conjectures.WangYangFussNarayanaDet

/-!
# Positivity Criteria and Galvin–Pacurar Change-of-Basis Theorem

Proves the three general structural results used in `results/wang-yang-fuss-narayana/proof.md`:
1. **Column criterion for STP**: if every minor on arbitrary increasing rows and consecutive
   columns is strictly positive, then every finite minor is strictly positive.
2. **Triangular minor test for TN**: if a finite lower-triangular matrix has strictly positive
   minors on initial columns `0, ..., k - 1` and any `k` consecutive rows, then it is TN.
3. **Galvin–Pacurar Theorem 1.2**: for nondecreasing target knots `b` and source knots `a`
   satisfying the cap condition `CapValid`, the Newton-basis change-of-basis matrix `C(a, b)`
   is totally nonnegative.
-/

namespace Conjectures.WangYangFussNarayana

open Matrix Finset
open scoped BigOperators

/-! ### Bordered-ones determinant identities -/

/-- Determinant of a matrix whose top row is all ones equals the determinant of its
adjacent column differences below row 0. -/
theorem det_border_row_zero_ones {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : ∀ j : Fin (k + 1), A 0 j = 1) :
    A.det = (Matrix.of fun i j : Fin k => A i.succ j.succ - A i.succ j.castSucc).det := by
  let B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
    fun i => Fin.cons (A i 0) (fun j => A i j.succ - A i j.castSucc)
  have hdet : A.det = B.det := by
    apply Matrix.det_eq_of_forall_col_eq_smul_add_pred (fun _ => (1 : ℝ))
    · intro i; simp [B]
    · intro i j; simp only [B, Fin.cons_succ]; ring
  have h00 : B 0 0 = 1 := by simp [B, hA]
  have h0s : ∀ j : Fin k, B 0 j.succ = 0 := fun j => by simp [B, hA]
  rw [hdet, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, h00, one_mul, Fin.succAbove_zero,
    h0s, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

/-- Determinant of a matrix whose first column is all ones equals the determinant of its
adjacent row differences to the right of column 0. -/
theorem det_border_col_zero_ones {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : ∀ i : Fin (k + 1), A i 0 = 1) :
    A.det = (Matrix.of fun i j : Fin k => A i.succ j.succ - A i.castSucc j.succ).det := by
  rw [← Matrix.det_transpose A, det_border_row_zero_ones Aᵀ (fun j => hA j),
    ← Matrix.det_transpose]
  congr 1

/-- Telescoping sum of adjacent differences over `Finset.Ico a b`. -/
theorem sum_Ico_diff (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ c ∈ Finset.Ico a b, (f (c + 1) - f c) = f b - f a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    ring

/-! ### Column criterion for strict total positivity -/

/-- Positivity of all consecutive-column minors up to order `p`. -/
def ConsecutiveColSTPUpto (p : ℕ) (M : Matrix ℕ ℕ ℝ) : Prop :=
  ∀ (k : ℕ), k ≤ p → ∀ (rows : Fin k → ℕ) (b : ℕ), StrictMono rows →
    0 < (Matrix.of fun i j : Fin k => M (rows i) (b + j.val)).det

theorem det_submatrix_pos_of_consecutiveColSTPUpto :
    ∀ (p : ℕ) (M : Matrix ℕ ℕ ℝ), ConsecutiveColSTPUpto p M →
      ∀ (rows cols : Fin p → ℕ), StrictMono rows → StrictMono cols →
        0 < (M.submatrix rows cols).det
  | 0, _, _, _, _, _, _ => by simp
  | p + 1, M, hM, rows, cols, hrows, hcols => by
    let r0 : ℕ := rows 0
    have htop_pos : ∀ c : ℕ, 0 < M r0 c := by
      intro c
      have h1 := hM 1 (by omega) (fun _ => r0) c (fun a b hab => by
        fin_cases a; fin_cases b; simp at hab)
      simpa [Matrix.det_fin_one] using h1
    let M₁ : Matrix ℕ ℕ ℝ := fun r c => M r c / M r0 c
    have hM₁_top : ∀ c : ℕ, M₁ r0 c = 1 := fun c => div_self (htop_pos c).ne'
    let D' : Matrix ℕ ℕ ℝ := fun i c => M₁ (r0 + 1 + i) (c + 1) - M₁ (r0 + 1 + i) c
    have hD' : ConsecutiveColSTPUpto p D' := by
      intro k hk u b hu
      let u_ext : Fin (k + 1) → ℕ := Fin.cons r0 (fun i => r0 + 1 + u i)
      have hu_ext : StrictMono u_ext := by
        apply Fin.strictMono_cons.mpr
        refine ⟨fun i => by omega, fun a b hab => ?_⟩
        have := hu hab
        dsimp only
        omega
      let A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
        Matrix.of fun i j => M₁ (u_ext i) (b + j.val)
      have hA_scale :
          A = (Matrix.of fun i j : Fin (k + 1) => M (u_ext i) (b + j.val)) *
            Matrix.diagonal (fun j : Fin (k + 1) => (M r0 (b + j.val))⁻¹) := by
        ext i j
        simp [A, M₁, Matrix.mul_diagonal, div_eq_mul_inv]
      have hA_pos : 0 < A.det := by
        rw [hA_scale, Matrix.det_mul, Matrix.det_diagonal]
        refine mul_pos (hM (k + 1) (by omega) u_ext b hu_ext) ?_
        exact Finset.prod_pos fun j _ => inv_pos.mpr (htop_pos (b + j.val))
      have hA_top : ∀ j : Fin (k + 1), A 0 j = 1 := fun j => by
        simp [A, u_ext, hM₁_top]
      rw [det_border_row_zero_ones A hA_top] at hA_pos
      have hA_eq :
          (Matrix.of fun i j : Fin k => D' (u i) (b + j.val)) =
            (Matrix.of fun i j : Fin k => A i.succ j.succ - A i.succ j.castSucc) := by
        ext i j
        simp only [Matrix.of_apply, D', A, u_ext, Fin.cons_succ, Fin.val_succ, Fin.val_castSucc]
        rw [Nat.add_assoc b j.val 1]
      rw [hA_eq]
      exact hA_pos
    -- Normalize columns of `M.submatrix rows cols` by `M r0 (cols j) > 0`.
    have hscale :
        M.submatrix rows cols =
          (M₁.submatrix rows cols) * Matrix.diagonal (fun j => M r0 (cols j)) := by
      ext i j
      simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, M₁]
      exact (div_mul_cancel₀ _ (htop_pos (cols j)).ne').symm
    rw [hscale, Matrix.det_mul, Matrix.det_diagonal]
    refine mul_pos ?_ (Finset.prod_pos fun j _ => htop_pos (cols j))
    rw [det_border_row_zero_ones (M₁.submatrix rows cols) (fun j => by
      simpa [r0] using hM₁_top (cols j))]
    -- Rewrite each column difference as a telescoping sum of `D'` columns.
    let rows' : Fin p → ℕ := fun i => rows i.succ - (r0 + 1)
    have hrows'_eq : ∀ i : Fin p, r0 + 1 + rows' i = rows i.succ := fun i => by
      have hlt : r0 < rows i.succ := hrows (Fin.succ_pos i)
      dsimp only [rows']
      omega
    have hrows' : StrictMono rows' := by
      intro a b hab
      have h1 := hrows'_eq a
      have h2 := hrows'_eq b
      have hlt : rows a.succ < rows b.succ := hrows (Fin.succ_lt_succ_iff.mpr hab)
      omega
    let I : Fin p → Finset ℕ := fun j => Finset.Ico (cols j.castSucc) (cols j.succ)
    have hmat_sum :
        (Matrix.of fun i j : Fin p =>
          (M₁.submatrix rows cols) i.succ j.succ -
            (M₁.submatrix rows cols) i.succ j.castSucc) =
          Matrix.of (fun i j : Fin p => ∑ c ∈ I j, D' (rows' i) c) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.of_apply, D', hrows'_eq, I]
      have hle : cols j.castSucc ≤ cols j.succ := (hcols Fin.castSucc_lt_succ).le
      exact (sum_Ico_diff (fun c => M₁ (rows i.succ) c) hle).symm
    rw [hmat_sum, det_sum_cols]
    have hnonempty : (Fintype.piFinset I).Nonempty := by
      refine ⟨fun j => cols j.castSucc, Fintype.mem_piFinset.mpr fun j => ?_⟩
      exact Finset.mem_Ico.mpr ⟨le_refl _, hcols Fin.castSucc_lt_succ⟩
    refine Finset.sum_pos (fun f hf => ?_) hnonempty
    have hf_mem := Fintype.mem_piFinset.mp hf
    have hf_mono : StrictMono f := by
      intro a b hab
      have ha : f a < cols a.succ := (Finset.mem_Ico.mp (hf_mem a)).2
      have hb : cols b.castSucc ≤ f b := (Finset.mem_Ico.mp (hf_mem b)).1
      have hle : a.succ ≤ b.castSucc := by
        rw [Fin.le_iff_val_le_val]
        simp only [Fin.val_succ, Fin.val_castSucc]
        exact hab
      have hcol_le : cols a.succ ≤ cols b.castSucc := hcols.monotone hle
      omega
    exact det_submatrix_pos_of_consecutiveColSTPUpto p D' hD' rows' f hrows' hf_mono

/-- **Column criterion**: if every consecutive-column minor of `M : Matrix ℕ ℕ ℝ` is strictly
positive, then `M` is strictly totally positive. -/
theorem isStrictlyTotallyPos_of_consecutive_cols {M : Matrix ℕ ℕ ℝ}
    (hM : ∀ (p : ℕ) (rows : Fin p → ℕ) (b : ℕ), StrictMono rows →
      0 < (Matrix.of fun i j : Fin p => M (rows i) (b + j.val)).det) :
    IsStrictlyTotallyPos M := by
  intro p rows cols hrows hcols
  exact det_submatrix_pos_of_consecutiveColSTPUpto p M (fun k _ => hM k) rows cols hrows hcols

/-! ### Triangular minor test for total nonnegativity -/

/-- **Triangular minor test**: a finite lower-triangular matrix whose initial-column,
consecutive-row minors are strictly positive is totally nonnegative. -/
theorem isTotallyNonneg_of_lowerTriangular_flag_pos :
    ∀ (N : ℕ) (L : Matrix (Fin N) (Fin N) ℝ),
      L.IsLowerTriangular →
      (∀ (k start : ℕ) (h : start + k ≤ N),
        0 < (Matrix.of fun i j : Fin k =>
          L ⟨start + i.val, by omega⟩ ⟨j.val, by omega⟩).det) →
      L.IsTotallyNonneg
  | 0, _, _, _ => by
    intro k rows cols _ _
    cases k with
    | zero => simp
    | succ k => exact Fin.elim0 (rows 0)
  | N + 1, L, htri, hflag => by
    have hcol0_pos : ∀ i : Fin (N + 1), 0 < L i 0 := by
      intro i
      have h1 := hflag 1 i.val (by omega)
      simpa [Matrix.det_fin_one] using h1
    let L₁ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun i j => L i j / L i 0
    have hL₁_col0 : ∀ i : Fin (N + 1), L₁ i 0 = 1 := fun i => div_self (hcol0_pos i).ne'
    have hL₁_tri : L₁.IsLowerTriangular := by
      intro i j hij
      simp [L₁, htri hij]
    let M : Matrix (Fin N) (Fin N) ℝ :=
      fun i j => L₁ i.succ j.succ - L₁ i.castSucc j.succ
    have hM_tri : M.IsLowerTriangular := by
      intro i j hij
      have hij' : i < j := hij
      have h1 : i.succ < j.succ := Fin.succ_lt_succ_iff.mpr hij'
      have h2 : i.castSucc < j.succ := lt_trans Fin.castSucc_lt_succ h1
      have hz1 : L₁ i.succ j.succ = 0 := hL₁_tri h1
      have hz2 : L₁ i.castSucc j.succ = 0 := hL₁_tri h2
      dsimp only [M]
      rw [hz1, hz2, sub_self]
    have hM_flag : ∀ (k start : ℕ) (h : start + k ≤ N),
        0 < (Matrix.of fun i j : Fin k =>
          M ⟨start + i.val, by omega⟩ ⟨j.val, by omega⟩).det := by
      intro k start h
      let A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
        Matrix.of fun i j => L₁ ⟨start + i.val, by omega⟩ ⟨j.val, by omega⟩
      have hA_scale :
          A = Matrix.diagonal (fun i : Fin (k + 1) => (L ⟨start + i.val, by omega⟩ 0)⁻¹) *
            Matrix.of (fun i j : Fin (k + 1) =>
              L ⟨start + i.val, by omega⟩ ⟨j.val, by omega⟩) := by
        ext i j
        simp [A, L₁, Matrix.diagonal_mul, div_eq_mul_inv, mul_comm]
      have hA_pos : 0 < A.det := by
        rw [hA_scale, Matrix.det_mul, Matrix.det_diagonal]
        refine mul_pos ?_ (hflag (k + 1) start (by omega))
        exact Finset.prod_pos fun i _ => inv_pos.mpr (hcol0_pos ⟨start + i.val, by omega⟩)
      have hA_col0 : ∀ i : Fin (k + 1), A i 0 = 1 := fun i => by
        simp [A, hL₁_col0]
      rw [det_border_col_zero_ones A hA_col0] at hA_pos
      have hM_eq :
          (Matrix.of fun i j : Fin k => M ⟨start + i.val, by omega⟩ ⟨j.val, by omega⟩) =
            (Matrix.of fun i j : Fin k => A i.succ j.succ - A i.castSucc j.succ) := by
        ext i j
        simp only [Matrix.of_apply, M, A, Fin.val_succ, Fin.val_castSucc]
        rfl
      rw [hM_eq]
      exact hA_pos
    have hM_TN : M.IsTotallyNonneg :=
      isTotallyNonneg_of_lowerTriangular_flag_pos N M hM_tri hM_flag
    have hL₁_eq : L₁ = lowerOnes (N + 1) * blockDiagOne M := by
      ext i j
      rw [Matrix.mul_apply]
      let g : ℕ → ℝ := fun r =>
        if hr : r < N + 1 then blockDiagOne M ⟨r, hr⟩ j else 0
      have hsum :
          (∑ r : Fin (N + 1), lowerOnes (N + 1) i r * blockDiagOne M r j) =
            ∑ r ∈ Finset.range (i.val + 1), g r := by
        have hconv :
            (∑ r : Fin (N + 1), lowerOnes (N + 1) i r * blockDiagOne M r j) =
              ∑ r ∈ Finset.range (N + 1),
                if hr : r < N + 1 then lowerOnes (N + 1) i ⟨r, hr⟩ * blockDiagOne M ⟨r, hr⟩ j else 0 := by
          rw [← Fin.sum_univ_eq_sum_range (fun r =>
            if hr : r < N + 1 then lowerOnes (N + 1) i ⟨r, hr⟩ * blockDiagOne M ⟨r, hr⟩ j else 0)]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [dite_eq_left r.isLt]
        rw [hconv]
        rw [← Finset.sum_subset (Finset.range_mono (by omega : i.val + 1 ≤ N + 1))]
        · refine Finset.sum_congr rfl fun r hr => ?_
          have hr1 : r < i.val + 1 := Finset.mem_range.mp hr
          have hrN : r < N + 1 := by omega
          have hle : (⟨r, hrN⟩ : Fin (N + 1)) ≤ i := by
            change r ≤ i.val; omega
          simp only [g, dite_eq_left hrN, lowerOnes, ite_eq_left hle, one_mul]
        · intro r hr hnot
          have hrN : r < N + 1 := Finset.mem_range.mp hr
          have hgt : ¬ r < i.val + 1 := fun h => hnot (Finset.mem_range.mpr h)
          have hnle : ¬ (⟨r, hrN⟩ : Fin (N + 1)) ≤ i := by
            change ¬ r ≤ i.val; omega
          simp only [dite_eq_left hrN, lowerOnes, ite_eq_right hnle, zero_mul]
      rw [hsum]
      have htel : ∀ (m : ℕ) (hm : m < N + 1),
          (∑ r ∈ Finset.range (m + 1), g r) = L₁ ⟨m, hm⟩ j := by
        intro m
        induction m with
        | zero =>
          intro hm
          rw [Finset.sum_range_one]
          dsimp only [g]
          rw [dite_eq_left hm]
          refine Fin.cases ?_ (fun j' => ?_) j
          · exact (hL₁_col0 0).symm
          · have hlt : (0 : Fin (N + 1)) < j'.succ := Fin.succ_pos j'
            exact (hL₁_tri hlt).symm
        | succ m ih =>
          intro hm
          rw [Finset.sum_range_succ, ih (by omega)]
          dsimp only [g]
          rw [dite_eq_left hm]
          refine Fin.cases ?_ (fun j' => ?_) j
          · have hsucc : (⟨m + 1, hm⟩ : Fin (N + 1)) = (⟨m, by omega⟩ : Fin N).succ := rfl
            rw [hsucc, blockDiagOne_succ_zero, add_zero, hL₁_col0, hL₁_col0]
          · have hsucc : (⟨m + 1, hm⟩ : Fin (N + 1)) = (⟨m, by omega⟩ : Fin N).succ := rfl
            rw [hsucc, blockDiagOne_succ_succ]
            simp only [M]
            have hcast : (⟨m, by omega⟩ : Fin N).castSucc = ⟨m, by omega⟩ := rfl
            rw [hcast]
            ring
      exact (htel i.val i.isLt).symm
    have hL₁_TN : L₁.IsTotallyNonneg := by
      rw [hL₁_eq]
      exact isTotallyNonneg_mul (lowerOnes_isTotallyNonneg (N + 1))
        (isTotallyNonneg_blockDiagOne hM_TN)
    exact isTotallyNonneg_of_row_col_scale hL₁_TN (r := fun i => L i 0) (c := fun _ => 1)
      (fun i => (hcol0_pos i).le) (fun _ => zero_le_one)
      (fun i j => by simp [L₁, mul_div_cancel₀ _ (hcol0_pos i).ne'])

/-! ### Galvin–Pacurar Theorem 1.2 (Newton basis change-of-basis) -/

/-- Coefficients `C(a, b)_{i, k}` expressing `∏_{r < i} (x - a r)` in the Newton basis
`{∏_{r < k} (x - b r)}`. -/
noncomputable def newtonChange (a b : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | i + 1, 0 => (b 0 - a i) * newtonChange a b i 0
  | i + 1, k + 1 => newtonChange a b i k + (b (k + 1) - a i) * newtonChange a b i (k + 1)

theorem newtonChange_eq_zero_of_lt (a b : ℕ → ℝ) {i k : ℕ} (h : i < k) :
    newtonChange a b i k = 0 := by
  induction i generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k => rfl
  | succ i ih =>
    cases k with
    | zero => omega
    | succ k =>
      simp only [newtonChange, ih (by omega : i < k), ih (by omega : i < k + 1),
        mul_zero, add_zero]

theorem sum_newtonChange_mul_newtonBasis (a b : ℕ → ℝ) (i : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (i + 1), newtonChange a b i k * newtonBasis b k x) =
      newtonBasis a i x := by
  induction i with
  | zero =>
    simp [newtonChange, newtonBasis]
  | succ i ih =>
    rw [newtonBasis_succ, ← ih, Finset.sum_mul]
    have hsplit : ∀ k,
        newtonChange a b i k * newtonBasis b k x * (x - a i) =
          (b k - a i) * newtonChange a b i k * newtonBasis b k x +
            newtonChange a b i k * newtonBasis b (k + 1) x := by
      intro k
      rw [newtonBasis_succ]
      ring
    simp_rw [hsplit, Finset.sum_add_distrib]
    have h1 :
        (∑ k ∈ Finset.range (i + 1), (b k - a i) * newtonChange a b i k * newtonBasis b k x) =
          ∑ k ∈ Finset.range (i + 2), (b k - a i) * newtonChange a b i k * newtonBasis b k x := by
      symm
      rw [Finset.sum_range_succ, newtonChange_eq_zero_of_lt a b (Nat.lt_succ_self i)]
      simp
    have h2 :
        (∑ k ∈ Finset.range (i + 1), newtonChange a b i k * newtonBasis b (k + 1) x) =
          ∑ k ∈ Finset.range (i + 2),
            (if k = 0 then (0 : ℝ) else newtonChange a b i (k - 1)) * newtonBasis b k x := by
      symm
      rw [Finset.sum_range_succ']
      simp
    rw [h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    cases k with
    | zero => simp [newtonChange]
    | succ k =>
      simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, newtonChange]
      ring

theorem newtonChange_succ_zero (a b : ℕ → ℝ) (i : ℕ) :
    newtonChange a b (i + 1) 0 = (b 0 - a i) * newtonChange a b i 0 := rfl

theorem newtonChange_succ_succ (a b : ℕ → ℝ) (i k : ℕ) :
    newtonChange a b (i + 1) (k + 1) =
      newtonChange a b i k + (b (k + 1) - a i) * newtonChange a b i (k + 1) := rfl

theorem newtonChange_shift_of_eq (a b : ℕ → ℝ) (h0 : a 0 = b 0) :
    ∀ i : ℕ,
      newtonChange a b (i + 1) 0 = 0 ∧
        ∀ k : ℕ, newtonChange a b (i + 1) (k + 1) =
          newtonChange (fun r => a (r + 1)) (fun r => b (r + 1)) i k := by
  intro i
  induction i with
  | zero =>
    refine ⟨by rw [newtonChange_succ_zero, h0, sub_self, zero_mul], fun k => ?_⟩
    cases k with
    | zero => simp [newtonChange]
    | succ k => simp [newtonChange]
  | succ i ih =>
    constructor
    · rw [newtonChange_succ_zero, ih.1, mul_zero]
    · intro k
      cases k with
      | zero =>
        rw [newtonChange_succ_succ, ih.1, ih.2 0, zero_add, newtonChange_succ_zero]
      | succ k =>
        rw [newtonChange_succ_succ, ih.2 k, ih.2 (k + 1), newtonChange_succ_succ]

theorem newtonChange_factor_first (a b : ℕ → ℝ) :
    ∀ i : ℕ,
      newtonChange a b (i + 1) 0 =
        (b 0 - a 0) * newtonChange (fun r => a (r + 1)) b i 0 ∧
      ∀ k : ℕ, newtonChange a b (i + 1) (k + 1) =
        newtonChange (fun r => a (r + 1)) b i k +
          (b (k + 1) - a 0) * newtonChange (fun r => a (r + 1)) b i (k + 1) := by
  intro i
  induction i with
  | zero =>
    refine ⟨by simp [newtonChange], fun k => ?_⟩
    cases k with
    | zero => simp [newtonChange]
    | succ k => simp [newtonChange]
  | succ i ih =>
    constructor
    · rw [newtonChange_succ_zero, ih.1, newtonChange_succ_zero]
      ring
    · intro k
      cases k with
      | zero =>
        rw [newtonChange_succ_succ, ih.1, ih.2 0, newtonChange_succ_zero, newtonChange_succ_succ]
        ring
      | succ k =>
        rw [newtonChange_succ_succ, ih.2 k, ih.2 (k + 1), newtonChange_succ_succ,
          newtonChange_succ_succ]
        ring

/-- Finite `N × N` Newton change-of-basis matrix. -/
noncomputable def newtonChangeMat (N : ℕ) (a b : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i k => newtonChange a b i.val k.val

/-- Galvin–Pacurar cap condition for `N` steps. -/
def CapValid : ℕ → (ℕ → ℝ) → (ℕ → ℝ) → Prop
  | 0, _, _ => True
  | N + 1, a, b =>
      (a 0 = b 0 ∧ CapValid N (fun r => a (r + 1)) (fun r => b (r + 1))) ∨
      (a 0 ≤ b 0 ∧ CapValid N (fun r => a (r + 1)) b)

/-- **Galvin–Pacurar Theorem 1.2**: if `b` is nondecreasing and `(a, b)` satisfies the
cap condition for `N` steps, then `newtonChangeMat N a b` is totally nonnegative. -/
theorem newtonChangeMat_isTotallyNonneg :
    ∀ (N : ℕ) (a b : ℕ → ℝ), Monotone b → CapValid N a b →
      (newtonChangeMat N a b).IsTotallyNonneg
  | 0, _, _, _, _ => by
    intro k rows cols _ _
    cases k with
    | zero => simp
    | succ k => exact Fin.elim0 (rows 0)
  | N + 1, a, b, hb, hcap => by
    rcases hcap with ⟨h0, hnext⟩ | ⟨hle, hnext⟩
    · have hmat :
          newtonChangeMat (N + 1) a b =
            blockDiagOne (newtonChangeMat N (fun r => a (r + 1)) (fun r => b (r + 1))) := by
        ext i k
        refine Fin.cases ?_ (fun i' => ?_) i
        · refine Fin.cases ?_ (fun k' => ?_) k
          · simp [newtonChangeMat, newtonChange]
          · simp [newtonChangeMat, newtonChange]
        · refine Fin.cases ?_ (fun k' => ?_) k
          · simp [newtonChangeMat, (newtonChange_shift_of_eq a b h0 i'.val).1]
          · simp [newtonChangeMat, (newtonChange_shift_of_eq a b h0 i'.val).2 k'.val]
      rw [hmat]
      have hb' : Monotone (fun r => b (r + 1)) := fun x y hxy => hb (Nat.add_le_add_right hxy 1)
      exact isTotallyNonneg_blockDiagOne (newtonChangeMat_isTotallyNonneg N _ _ hb' hnext)
    · let C' := newtonChangeMat N (fun r => a (r + 1)) b
      let d : Fin N → ℝ := fun r => b r.val - a 0
      have hd : ∀ r : Fin N, 0 ≤ d r := fun r => by
        have hbr : b 0 ≤ b r.val := hb (Nat.zero_le r.val)
        dsimp only [d]
        linarith
      have hmat :
          newtonChangeMat (N + 1) a b = blockDiagOne C' * lowerBidiag N d := by
        ext i j
        rw [Matrix.mul_apply]
        refine Fin.cases ?_ (fun i' => ?_) i
        · rw [Finset.sum_eq_single (0 : Fin (N + 1))]
          · refine Fin.cases ?_ (fun j' => ?_) j
            · simp [newtonChangeMat, newtonChange, lowerBidiag]
            · have hne : (0 : Fin (N + 1)) ≠ j'.succ := (Fin.succ_ne_zero j').symm
              simp [newtonChangeMat, newtonChange, lowerBidiag, hne]
          · intro r _ hr
            obtain ⟨r', rfl⟩ := Fin.eq_succ_of_ne_zero hr
            simp
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [Fin.sum_univ_succ, blockDiagOne_succ_zero, zero_mul, zero_add]
          simp_rw [blockDiagOne_succ_succ]
          refine Fin.cases ?_ (fun j' => ?_) j
          · let r0 : Fin N := ⟨0, Nat.zero_lt_of_lt i'.isLt⟩
            rw [Finset.sum_eq_single r0]
            · have hLB : lowerBidiag N d r0.succ 0 = b 0 - a 0 := by
                unfold lowerBidiag
                rw [ite_eq_right (Fin.succ_ne_zero r0), dite_eq_left (by simp [r0])]
                rfl
              rw [hLB]
              simp only [C', newtonChangeMat, Fin.val_succ, Fin.val_zero]
              rw [(newtonChange_factor_first a b i'.val).1]
              ring
            · intro r _ hr
              have hne : r.succ ≠ (0 : Fin (N + 1)) := Fin.succ_ne_zero r
              have hval : r.val ≠ 0 := fun h => hr (Fin.ext h)
              simp [lowerBidiag, hne, hval]
            · intro h; exact absurd (Finset.mem_univ _) h
          · by_cases hj : j'.val + 1 < N
            · let jnext : Fin N := ⟨j'.val + 1, hj⟩
              have hne : j' ≠ jnext := fun h => by
                have := congrArg Fin.val h
                dsimp [jnext] at this
                omega
              rw [Finset.sum_eq_add j' jnext hne]
              · have h1 : lowerBidiag N d j'.succ j'.succ = 1 := by simp [lowerBidiag]
                have h2 : lowerBidiag N d jnext.succ j'.succ = b (j'.val + 1) - a 0 := by
                  have hne' : jnext.succ ≠ j'.succ := fun h => hne (Fin.succ_injective _ h).symm
                  unfold lowerBidiag
                  rw [ite_eq_right hne', dite_eq_left (by simp [jnext])]
                  rfl
                rw [h1, h2, mul_one]
                simp only [C', newtonChangeMat, jnext, Fin.val_succ]
                rw [(newtonChange_factor_first a b i'.val).2 j'.val]
                ring
              · intro r _ hpair
                have hr1 : r.succ ≠ j'.succ := fun h => hpair.1 (Fin.succ_injective _ h)
                have hr2 : r.val ≠ j'.val + 1 := fun h => hpair.2 (Fin.ext h)
                simp [lowerBidiag, hr1, hr2]
              · intro h; exact absurd (Finset.mem_univ _) h
              · intro h; exact absurd (Finset.mem_univ _) h
            · rw [Finset.sum_eq_single j']
              · have h1 : lowerBidiag N d j'.succ j'.succ = 1 := by simp [lowerBidiag]
                rw [h1, mul_one]
                simp only [C', newtonChangeMat, Fin.val_succ]
                rw [(newtonChange_factor_first a b i'.val).2 j'.val]
                have hzero : newtonChange (fun r => a (r + 1)) b i'.val (j'.val + 1) = 0 :=
                  newtonChange_eq_zero_of_lt _ _ (by omega)
                rw [hzero, mul_zero, add_zero]
              · intro r _ hr
                have hr1 : r.succ ≠ j'.succ := fun h => hr (Fin.succ_injective _ h)
                have hr2 : r.val ≠ j'.val + 1 := by omega
                simp [lowerBidiag, hr1, hr2]
              · intro h; exact absurd (Finset.mem_univ _) h
      rw [hmat]
      exact isTotallyNonneg_mul
        (isTotallyNonneg_blockDiagOne (newtonChangeMat_isTotallyNonneg N _ _ hb hnext))
        (lowerBidiag_isTotallyNonneg N hd)

end Conjectures.WangYangFussNarayana
