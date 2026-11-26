import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyNonneg
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Total Positivity and Total Nonnegativity Matrix Tools

General determinant and total-positivity primitives used in the proof of
Wang–Yang's Fuss–Narayana conjecture:
- `IsStrictlyTotallyPos` (strict positivity of every finite minor);
- row/column positive scaling, finite-section lifts, and topological limits of TN matrices;
- column multilinearity of determinants;
- the Cauchy–Binet formula and closure of `Matrix.IsTotallyNonneg` under finite matrix products;
- block-diagonal extension `blockDiagOne`, elementary subdiagonal additions `I + c E_{1, 0}`,
  lower-triangular all-ones matrices, and nonnegative lower-bidiagonal matrices.
-/

namespace Conjectures.WangYangFussNarayana

open Matrix Filter Topology Finset
open scoped BigOperators

/-- A matrix is strictly totally positive (STP) if every finite minor has strictly positive
determinant. -/
def IsStrictlyTotallyPos {ι R : Type*} [PartialOrder ι] [CommRing R] [PartialOrder R]
    (M : Matrix ι ι R) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃rows cols : Fin n → ι⦄, StrictMono rows → StrictMono cols →
    0 < (M.submatrix rows cols).det

theorem IsStrictlyTotallyPos.submatrix {ι κ R : Type*} [PartialOrder ι] [PartialOrder κ]
    [CommRing R] [PartialOrder R] {M : Matrix ι ι R} {f g : κ → ι}
    (hM : IsStrictlyTotallyPos M) (hf : StrictMono f) (hg : StrictMono g) :
    IsStrictlyTotallyPos (M.submatrix f g) :=
  fun _ _ _ hrows hcols => by simpa using hM (hf.comp hrows) (hg.comp hcols)

theorem IsStrictlyTotallyPos.isTotallyNonneg {ι R : Type*} [PartialOrder ι]
    [CommRing R] [PartialOrder R] {M : Matrix ι ι R} (hM : IsStrictlyTotallyPos M) :
    M.IsTotallyNonneg :=
  fun _ _ _ hrows hcols => (hM hrows hcols).le

theorem det_submatrix_row_col_scale {ι R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix ι ι R) (r c : ι → R) (rows cols : Fin n → ι) :
    ((Matrix.of fun i j => r i * M i j * c j).submatrix rows cols).det =
      (∏ i : Fin n, r (rows i)) * (M.submatrix rows cols).det * (∏ j : Fin n, c (cols j)) := by
  have hmat :
      (Matrix.of fun i j => r i * M i j * c j).submatrix rows cols =
        Matrix.diagonal (fun i => r (rows i)) * (M.submatrix rows cols) *
          Matrix.diagonal (fun j => c (cols j)) := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]

theorem IsStrictlyTotallyPos.of_row_col_scale {ι : Type*} [PartialOrder ι]
    {M N : Matrix ι ι ℝ} {r c : ι → ℝ}
    (hN : IsStrictlyTotallyPos N)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hMN : ∀ i j, M i j = r i * N i j * c j) :
    IsStrictlyTotallyPos M := by
  intro n rows cols hrows hcols
  have hM : M = Matrix.of (fun i j => r i * N i j * c j) := by
    ext i j
    exact hMN i j
  rw [hM, det_submatrix_row_col_scale]
  have hrp : 0 < ∏ i : Fin n, r (rows i) := Finset.prod_pos fun i _ => hr (rows i)
  have hcp : 0 < ∏ j : Fin n, c (cols j) := Finset.prod_pos fun j _ => hc (cols j)
  exact mul_pos (mul_pos hrp (hN hrows hcols)) hcp

theorem isTotallyNonneg_of_row_col_scale {ι : Type*} [PartialOrder ι]
    {M N : Matrix ι ι ℝ} {r c : ι → ℝ}
    (hN : N.IsTotallyNonneg)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ j, 0 ≤ c j)
    (hMN : ∀ i j, M i j = r i * N i j * c j) :
    M.IsTotallyNonneg := by
  intro n rows cols hrows hcols
  have hM : M = Matrix.of (fun i j => r i * N i j * c j) := by
    ext i j
    exact hMN i j
  rw [hM, det_submatrix_row_col_scale]
  have hrp : 0 ≤ ∏ i : Fin n, r (rows i) := Finset.prod_nonneg fun i _ => hr (rows i)
  have hcp : 0 ≤ ∏ j : Fin n, c (cols j) := Finset.prod_nonneg fun j _ => hc (cols j)
  exact mul_nonneg (mul_nonneg hrp (hN hrows hcols)) hcp

/-- A `ℕ × ℕ` matrix is TN if every leading `N × N` finite section is TN. -/
theorem isTotallyNonneg_of_fin_sections {M : Matrix ℕ ℕ ℝ}
    (hM : ∀ N : ℕ, (M.submatrix (Fin.val : Fin N → ℕ) Fin.val).IsTotallyNonneg) :
    M.IsTotallyNonneg := by
  intro k rows cols hrows hcols
  let g : Fin k → ℕ := fun i => max (rows i) (cols i)
  let N : ℕ := Finset.univ.sup g + 1
  have hr_lt : ∀ i : Fin k, rows i < N := fun i => by
    have hle : g i ≤ Finset.univ.sup g := Finset.le_sup (f := g) (Finset.mem_univ i)
    exact Nat.lt_succ_of_le (le_trans (le_max_left _ _) hle)
  have hc_lt : ∀ j : Fin k, cols j < N := fun j => by
    have hle : g j ≤ Finset.univ.sup g := Finset.le_sup (f := g) (Finset.mem_univ j)
    exact Nat.lt_succ_of_le (le_trans (le_max_right _ _) hle)
  let rows' : Fin k → Fin N := fun i => ⟨rows i, hr_lt i⟩
  let cols' : Fin k → Fin N := fun j => ⟨cols j, hc_lt j⟩
  have hrows' : StrictMono rows' := fun a b hab => hrows hab
  have hcols' : StrictMono cols' := fun a b hab => hcols hab
  have hsub :
      (M.submatrix (Fin.val : Fin N → ℕ) Fin.val).submatrix rows' cols' =
        M.submatrix rows cols := by
    ext i j
    rfl
  rw [← hsub]
  exact hM N hrows' hcols'

/-- Pointwise limit of totally nonnegative matrices is totally nonnegative. -/
theorem isTotallyNonneg_of_tendsto {α : Type*} {N : ℕ} {l : Filter α} [l.NeBot]
    {M : α → Matrix (Fin N) (Fin N) ℝ} {L : Matrix (Fin N) (Fin N) ℝ}
    (hlim : Tendsto M l (𝓝 L))
    (hTN : ∀ᶠ a in l, (M a).IsTotallyNonneg) :
    L.IsTotallyNonneg := by
  intro k rows cols hrows hcols
  have hsub : Tendsto (fun a => (M a).submatrix rows cols) l (𝓝 (L.submatrix rows cols)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim (rows i)) (cols j)
  have hdet : Tendsto (fun a => ((M a).submatrix rows cols).det) l
      (𝓝 ((L.submatrix rows cols).det)) :=
    (continuous_id.matrix_det.tendsto _).comp hsub
  exact ge_of_tendsto hdet (hTN.mono fun a ha => ha hrows hcols)

/-- Column multilinearity of the determinant over finite index families. -/
theorem det_sum_cols {p : ℕ} {α : Type*} (I : Fin p → Finset α) (G : Fin p → α → ℝ) :
    (Matrix.of fun i j : Fin p => ∑ c ∈ I j, G i c).det =
      ∑ f ∈ Fintype.piFinset I, (Matrix.of fun i j : Fin p => G i (f j)).det := by
  simp_rw [Matrix.det_apply', Matrix.of_apply, Finset.prod_univ_sum, Finset.mul_sum]
  exact Finset.sum_comm

/-- Strictly monotone permutation of `Fin k` is the identity. -/
theorem strictMono_perm_eq_one {k : ℕ} (σ : Equiv.Perm (Fin k)) (hσ : StrictMono σ) :
    σ = 1 := by
  ext i
  have hle : ∀ x : Fin k, x ≤ σ x := hσ.id_le
  have hsum : ∑ x : Fin k, (σ x).val = ∑ x : Fin k, x.val :=
    Equiv.sum_comp σ (fun x : Fin k => x.val)
  by_contra hne
  have hlt : i.val < (σ i).val := by
    have hi : i.val ≤ (σ i).val := hle i
    have hne' : (σ i).val ≠ i.val := by simpa using hne
    omega
  have hsum_lt : ∑ x : Fin k, x.val < ∑ x : Fin k, (σ x).val :=
    Finset.sum_lt_sum (fun x _ => hle x) ⟨i, Finset.mem_univ i, hlt⟩
  omega

/-- The Cauchy–Binet determinant identity for rectangular matrices over any commutative ring. -/
theorem det_mul_cauchyBinet {k N : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin k) (Fin N) R) (B : Matrix (Fin N) (Fin k) R) :
    (A * B).det =
      ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
        if hs : s.card = k then
          (A.submatrix id (s.orderEmbOfFin hs)).det * (B.submatrix (s.orderEmbOfFin hs) id).det
        else 0 := by
  classical
  -- Step 1: Expand `(A * B).det` over all functions `f : Fin k → Fin N`.
  have hstep1 :
      (A * B).det = ∑ f : Fin k → Fin N, (∏ i : Fin k, A i (f i)) * (B.submatrix f id).det := by
    rw [← Matrix.det_transpose (A * B), Matrix.det_apply']
    have hprod : ∀ σ : Equiv.Perm (Fin k),
        ∏ i : Fin k, (A * B)ᵀ (σ i) i =
          ∑ f : Fin k → Fin N, (∏ i : Fin k, A i (f i)) * ∏ i : Fin k, B (f i) (σ i) := by
      intro σ
      simp_rw [Matrix.transpose_apply, Matrix.mul_apply]
      rw [Fintype.prod_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← Finset.prod_mul_distrib]
    simp_rw [hprod, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← Matrix.det_transpose (B.submatrix f id), Matrix.det_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
    ring
  rw [hstep1]
  -- Step 2: Restrict to injective functions `f : Fin k → Fin N`.
  let injSet : Finset (Fin k → Fin N) := Finset.univ.filter Function.Injective
  have hinj :
      (∑ f : Fin k → Fin N, (∏ i : Fin k, A i (f i)) * (B.submatrix f id).det) =
        ∑ f ∈ injSet, (∏ i : Fin k, A i (f i)) * (B.submatrix f id).det := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun f _ hf => ?_
    have hnotinj : ¬ Function.Injective f := by
      simpa [injSet] using hf
    unfold Function.Injective at hnotinj
    push Not at hnotinj
    obtain ⟨i, j, hij, hne⟩ := hnotinj
    have hrow : (B.submatrix f id) i = (B.submatrix f id) j := by
      ext c
      simp [hij]
    rw [Matrix.det_zero_of_row_eq hne hrow, mul_zero]
  rw [hinj]
  -- Step 3: Partition `injSet` by the image `s = Finset.image f Finset.univ`.
  have hpart :
      (∑ f ∈ injSet, (∏ i : Fin k, A i (f i)) * (B.submatrix f id).det) =
        ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
          ∑ f ∈ injSet.filter (fun f => Finset.univ.image f = s),
            (∏ i : Fin k, A i (f i)) * (B.submatrix f id).det := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := injSet)
      (t := (Finset.univ : Finset (Fin N)).powersetCard k)
      (g := fun f => Finset.univ.image f)]
    intro f hf
    have hfi : Function.Injective f := (Finset.mem_filter.mp hf).2
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ hfi, Finset.card_univ, Fintype.card_fin]
  rw [hpart]
  -- Step 4: Evaluate each fiber via the bijection `τ ↦ s.orderEmbOfFin hs ∘ τ`.
  refine Finset.sum_congr rfl fun s hs => ?_
  have hcard : s.card = k := (Finset.mem_powersetCard.mp hs).2
  rw [dite_eq_left hcard]
  let e : Fin k ↪o Fin N := s.orderEmbOfFin hcard
  have hrange : Finset.univ.image e = s := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact Finset.orderEmbOfFin_mem s hcard i
    · intro hx
      have hx' : x ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin s hcard]
        exact hx
      exact hx'
  have hfiber :
      (∑ f ∈ injSet.filter (fun f => Finset.univ.image f = s),
          (∏ i : Fin k, A i (f i)) * (B.submatrix f id).det) =
        ∑ τ : Equiv.Perm (Fin k),
          (∏ i : Fin k, A i (e (τ i))) * (B.submatrix (fun i => e (τ i)) id).det := by
    symm
    refine Finset.sum_bij (fun τ _ => fun i => e (τ i)) ?_ ?_ ?_ ?_
    · intro τ _
      simp only [injSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨e.injective.comp τ.injective, ?_⟩
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      rw [← hrange]
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun ⟨i, hi⟩ => ⟨τ i, hi⟩, fun ⟨j, hj⟩ => ⟨τ.symm j, by simpa using hj⟩⟩
    · intro τ₁ _ τ₂ _ h
      apply Equiv.ext
      intro i
      have hi : e (τ₁ i) = e (τ₂ i) := congrFun h i
      exact e.injective hi
    · intro f hf
      simp only [injSet, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      obtain ⟨hfi, himg⟩ := hf
      have hex : ∀ i : Fin k, ∃ j : Fin k, e j = f i := by
        intro i
        have hmem : f i ∈ Finset.univ.image e := by
          rw [hrange, ← himg]
          exact Finset.mem_image_of_mem f (Finset.mem_univ i)
        simpa using hmem
      choose g hg using hex
      have hgi : Function.Injective g := by
        intro i₁ i₂ h
        apply hfi
        rw [← hg i₁, ← hg i₂, h]
      let τ : Equiv.Perm (Fin k) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hgi)
      refine ⟨τ, Finset.mem_univ _, ?_⟩
      funext i
      exact hg i
    · intro τ _
      rfl
  rw [hfiber]
  have hperm : ∀ τ : Equiv.Perm (Fin k),
      (B.submatrix (fun i => e (τ i)) id).det =
        (Equiv.Perm.sign τ : R) * (B.submatrix e id).det := by
    intro τ
    have hsub : B.submatrix (fun i => e (τ i)) id = (B.submatrix e id).submatrix τ id := by
      ext i j
      rfl
    rw [hsub, Matrix.det_permute]
  simp_rw [hperm]
  have hA_det :
      (A.submatrix id e).det =
        ∑ τ : Equiv.Perm (Fin k), (Equiv.Perm.sign τ : R) * ∏ i : Fin k, A i (e (τ i)) := by
    rw [← Matrix.det_transpose (A.submatrix id e), Matrix.det_apply']
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp [Matrix.transpose_apply, Matrix.submatrix_apply]
  rw [hA_det, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

/-- The product of two finite totally nonnegative matrices is totally nonnegative. -/
theorem isTotallyNonneg_mul {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsTotallyNonneg) (hB : B.IsTotallyNonneg) :
    (A * B).IsTotallyNonneg := by
  intro k rows cols hrows hcols
  have hsub : (A * B).submatrix rows cols = A.submatrix rows id * B.submatrix id cols := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hsub, det_mul_cauchyBinet]
  refine Finset.sum_nonneg fun s _ => ?_
  split_ifs with hs
  · have he : StrictMono (s.orderEmbOfFin hs) := (s.orderEmbOfFin hs).strictMono
    have h1 : 0 ≤ ((A.submatrix rows id).submatrix id (s.orderEmbOfFin hs)).det := by
      simpa using hA hrows he
    have h2 : 0 ≤ ((B.submatrix id cols).submatrix (s.orderEmbOfFin hs) id).det := by
      simpa using hB he hcols
    exact mul_nonneg h1 h2
  · exact le_refl 0

/-- Block-diagonal extension `diag(1, M)` of an `N × N` matrix to `(N + 1) × (N + 1)`. -/
def blockDiagOne {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j =>
    Fin.cases
      (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases 0 (fun j' => M i' j') j)
      i

@[simp] theorem blockDiagOne_zero_zero {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    blockDiagOne M 0 0 = 1 := rfl

@[simp] theorem blockDiagOne_zero_succ {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (j : Fin N) :
    blockDiagOne M 0 j.succ = 0 := rfl

@[simp] theorem blockDiagOne_succ_zero {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) :
    blockDiagOne M i.succ 0 = 0 := rfl

@[simp] theorem blockDiagOne_succ_succ {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    blockDiagOne M i.succ j.succ = M i j := rfl

theorem isTotallyNonneg_blockDiagOne {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ}
    (hM : M.IsTotallyNonneg) : (blockDiagOne M).IsTotallyNonneg := by
  intro k rows cols hrows hcols
  cases k with
  | zero => simp
  | succ k =>
    by_cases hr0 : rows 0 = 0
    · by_cases hc0 : cols 0 = 0
      · -- Both start at 0: expand along row 0.
        rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
        have htop : (blockDiagOne M).submatrix rows cols 0 0 = 1 := by
          simp [hr0, hc0]
        have hzero : ∀ j : Fin k, (blockDiagOne M).submatrix rows cols 0 j.succ = 0 := by
          intro j
          have hpos : (0 : Fin (N + 1)) < cols j.succ := by
            rw [← hc0]
            exact hcols (Fin.succ_pos j)
          obtain ⟨j', hj'⟩ := Fin.eq_succ_of_ne_zero (ne_of_gt hpos)
          simp [hr0, hj']
        simp only [Fin.val_zero, pow_zero, htop, one_mul, Fin.succAbove_zero,
          hzero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
        have hr_pos : ∀ i : Fin k, rows i.succ ≠ 0 := fun i => by
          rw [← hr0]
          exact ne_of_gt (hrows (Fin.succ_pos i))
        have hc_pos : ∀ j : Fin k, cols j.succ ≠ 0 := fun j => by
          rw [← hc0]
          exact ne_of_gt (hcols (Fin.succ_pos j))
        let rows' : Fin k → Fin N := fun i => (rows i.succ).pred (hr_pos i)
        let cols' : Fin k → Fin N := fun j => (cols j.succ).pred (hc_pos j)
        have hrows' : StrictMono rows' := fun a b hab =>
          Fin.pred_lt_pred_iff.mpr (hrows (Fin.succ_lt_succ_iff.mpr hab))
        have hcols' : StrictMono cols' := fun a b hab =>
          Fin.pred_lt_pred_iff.mpr (hcols (Fin.succ_lt_succ_iff.mpr hab))
        have hsub :
            ((blockDiagOne M).submatrix rows cols).submatrix Fin.succ Fin.succ =
              M.submatrix rows' cols' := by
          ext i j
          simp only [Matrix.submatrix_apply]
          have hi : rows i.succ = (rows' i).succ := (Fin.succ_pred _ _).symm
          have hj : cols j.succ = (cols' j).succ := (Fin.succ_pred _ _).symm
          rw [hi, hj, blockDiagOne_succ_succ]
        rw [hsub]
        exact hM hrows' hcols'
      · -- Row 0 is all zero since `cols j > 0` for all `j`.
        have hrow0 : ∀ j : Fin (k + 1), (blockDiagOne M).submatrix rows cols 0 j = 0 := by
          intro j
          have hc_ne : cols j ≠ 0 := by
            rcases eq_or_lt_of_le (Fin.zero_le j) with rfl | hlt
            · exact hc0
            · exact ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) (hcols hlt))
          obtain ⟨j', hj'⟩ := Fin.eq_succ_of_ne_zero hc_ne
          simp [hr0, hj']
        rw [Matrix.det_eq_zero_of_row_eq_zero 0 hrow0]
    · by_cases hc0 : cols 0 = 0
      · -- Column 0 is all zero since `rows i > 0` for all `i`.
        have hcol0 : ∀ i : Fin (k + 1), (blockDiagOne M).submatrix rows cols i 0 = 0 := by
          intro i
          have hr_ne : rows i ≠ 0 := by
            rcases eq_or_lt_of_le (Fin.zero_le i) with rfl | hlt
            · exact hr0
            · exact ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) (hrows hlt))
          obtain ⟨i', hi'⟩ := Fin.eq_succ_of_ne_zero hr_ne
          simp [hc0, hi']
        rw [Matrix.det_eq_zero_of_column_eq_zero 0 hcol0]
      · -- Neither starts at 0: entire minor lies inside `M`.
        have hr_ne : ∀ i : Fin (k + 1), rows i ≠ 0 := fun i => by
          rcases eq_or_lt_of_le (Fin.zero_le i) with rfl | hlt
          · exact hr0
          · exact ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) (hrows hlt))
        have hc_ne : ∀ j : Fin (k + 1), cols j ≠ 0 := fun j => by
          rcases eq_or_lt_of_le (Fin.zero_le j) with rfl | hlt
          · exact hc0
          · exact ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) (hcols hlt))
        let rows' : Fin (k + 1) → Fin N := fun i => (rows i).pred (hr_ne i)
        let cols' : Fin (k + 1) → Fin N := fun j => (cols j).pred (hc_ne j)
        have hrows' : StrictMono rows' := fun a b hab =>
          Fin.pred_lt_pred_iff.mpr (hrows hab)
        have hcols' : StrictMono cols' := fun a b hab =>
          Fin.pred_lt_pred_iff.mpr (hcols hab)
        have hsub : (blockDiagOne M).submatrix rows cols = M.submatrix rows' cols' := by
          ext i j
          simp only [Matrix.submatrix_apply]
          have hi : rows i = (rows' i).succ := (Fin.succ_pred _ _).symm
          have hj : cols j = (cols' j).succ := (Fin.succ_pred _ _).symm
          rw [hi, hj, blockDiagOne_succ_succ]
        rw [hsub]
        exact hM hrows' hcols'

/-- Elementary matrix `I + c E_{1, 0}` of size `(N + 2) × (N + 2)`. -/
def elemSubdiag0 (N : ℕ) (c : ℝ) : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ :=
  fun i j => if i = j then 1 else if i.val = 1 ∧ j.val = 0 then c else 0

theorem elemSubdiag0_isTotallyNonneg (N : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    (elemSubdiag0 N c).IsTotallyNonneg := by
  intro k rows cols hrows hcols
  let A : Matrix (Fin k) (Fin k) ℝ := (elemSubdiag0 N c).submatrix rows cols
  change 0 ≤ A.det
  rw [Matrix.det_apply']
  -- Every permutation with a nonzero term in `A.det` must be strictly monotone, hence `1`.
  have hsingle :
      (∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * ∏ i : Fin k, A (σ i) i) =
        ∏ i : Fin k, A i i := by
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin k))]
    · simp
    · intro σ _ hσne
      by_cases hprod : ∏ i : Fin k, A (σ i) i = 0
      · rw [hprod, mul_zero]
      · exfalso
        have hentry : ∀ i : Fin k, A (σ i) i ≠ 0 := fun i =>
          Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
        have hcase : ∀ i : Fin k,
            rows (σ i) = cols i ∨ ((rows (σ i)).val = 1 ∧ (cols i).val = 0) := by
          intro i
          have h := hentry i
          simp only [A, Matrix.submatrix_apply, elemSubdiag0] at h
          split_ifs at h with h1 h2
          · exact Or.inl h1
          · exact Or.inr h2
          · exact absurd rfl h
        have hmono : StrictMono σ := by
          intro a b hab
          have hcol_lt : (cols a).val < (cols b).val := hcols hab
          have hrow_lt : (rows (σ a)).val < (rows (σ b)).val := by
            rcases hcase a with ha | ⟨ha1, ha0⟩ <;> rcases hcase b with hb | ⟨hb1, hb0⟩
            · rw [ha, hb]; exact hcol_lt
            · omega
            · rw [ha1, hb]
              have hne1 : (cols b).val ≠ 1 := by
                intro h1
                have hrb : rows (σ b) = rows (σ a) := by
                  ext; omega
                have : σ b = σ a := hrows.injective hrb
                have : b = a := σ.injective this
                omega
              omega
            · omega
          exact hrows.lt_iff_lt.mp hrow_lt
        exact hσne (strictMono_perm_eq_one σ hmono)
    · intro h
      exact absurd (Finset.mem_univ 1) h
  rw [hsingle]
  refine Finset.prod_nonneg fun i _ => ?_
  simp only [A, Matrix.submatrix_apply, elemSubdiag0]
  split_ifs <;> linarith

/-- Lower-triangular all-ones matrix of size `N × N`. -/
def lowerOnes (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if j ≤ i then 1 else 0

theorem lowerOnes_isTotallyNonneg (N : ℕ) : (lowerOnes N).IsTotallyNonneg := by
  induction N with
  | zero =>
    intro k rows cols _ _
    cases k with
    | zero => simp
    | succ k => exact Fin.elim0 (rows 0)
  | succ N ih =>
    cases N with
    | zero =>
      have h1 : lowerOnes 1 = 1 := by
        ext i j
        fin_cases i; fin_cases j
        simp [lowerOnes]
      rw [h1]
      exact Matrix.IsTotallyNonneg.one
    | succ N =>
      have hfac : lowerOnes (N + 2) = blockDiagOne (lowerOnes (N + 1)) * elemSubdiag0 N 1 := by
        ext i j
        rw [Matrix.mul_apply]
        refine Fin.cases ?_ (fun i' => ?_) i
        · refine Fin.cases ?_ (fun j' => ?_) j
          · rw [Finset.sum_eq_single (0 : Fin (N + 2))]
            · simp [lowerOnes, elemSubdiag0]
            · intro k _ hk
              obtain ⟨k', rfl⟩ := Fin.eq_succ_of_ne_zero hk
              simp
            · intro h; exact absurd (Finset.mem_univ _) h
          · rw [Finset.sum_eq_single (0 : Fin (N + 2))]
            · have hne : (0 : Fin (N + 2)) ≠ j'.succ := (Fin.succ_ne_zero j').symm
              simp [lowerOnes, elemSubdiag0, hne]
            · intro k _ hk
              obtain ⟨k', rfl⟩ := Fin.eq_succ_of_ne_zero hk
              simp
            · intro h; exact absurd (Finset.mem_univ _) h
        · refine Fin.cases ?_ (fun j' => ?_) j
          · rw [Finset.sum_eq_single (1 : Fin (N + 2))]
            · have hle : (0 : Fin (N + 1)) ≤ i' := Fin.zero_le i'
              have h1 : (1 : Fin (N + 2)) = (0 : Fin (N + 1)).succ := rfl
              rw [h1, blockDiagOne_succ_succ]
              simp [lowerOnes, elemSubdiag0, hle]
            · intro k _ hk
              have hzero : elemSubdiag0 N 1 k 0 = 0 ∨ blockDiagOne (lowerOnes (N + 1)) i'.succ k = 0 := by
                by_cases hk0 : k = 0
                · subst hk0; exact Or.inr (blockDiagOne_succ_zero _ _)
                · left
                  simp only [elemSubdiag0, hk0, ite_false, Fin.val_zero, and_true]
                  have hk1 : k.val ≠ 1 := fun h => hk (Fin.ext h)
                  simp [hk1]
              rcases hzero with h | h <;> simp [h]
            · intro h; exact absurd (Finset.mem_univ _) h
          · rw [Finset.sum_eq_single j'.succ]
            · have hE : elemSubdiag0 N 1 j'.succ j'.succ = 1 := by simp [elemSubdiag0]
              rw [blockDiagOne_succ_succ, hE, mul_one]
              simp [lowerOnes, Fin.succ_le_succ_iff]
            · intro k _ hk
              have hE : elemSubdiag0 N 1 k j'.succ = 0 := by
                simp [elemSubdiag0, hk]
              rw [hE, mul_zero]
            · intro h; exact absurd (Finset.mem_univ _) h
      rw [hfac]
      exact isTotallyNonneg_mul (isTotallyNonneg_blockDiagOne ih)
        (elemSubdiag0_isTotallyNonneg N zero_le_one)

/-- Lower-bidiagonal matrix of size `(N + 1) × (N + 1)` with ones on the diagonal and
`d r` at `(r.succ, r.castSucc)`. -/
def lowerBidiag (N : ℕ) (d : Fin N → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j =>
    if i = j then 1
    else if h : i.val = j.val + 1 then d ⟨j.val, by omega⟩
    else 0

theorem lowerBidiag_isTotallyNonneg (N : ℕ) {d : Fin N → ℝ} (hd : ∀ r, 0 ≤ d r) :
    (lowerBidiag N d).IsTotallyNonneg := by
  induction N with
  | zero =>
    have h1 : lowerBidiag 0 d = 1 := by
      ext i j
      fin_cases i; fin_cases j
      simp [lowerBidiag]
    rw [h1]
    exact Matrix.IsTotallyNonneg.one
  | succ N ih =>
    have hfac :
        lowerBidiag (N + 1) d =
          elemSubdiag0 N (d 0) * blockDiagOne (lowerBidiag N (fun r => d r.succ)) := by
      ext i j
      rw [Matrix.mul_apply]
      refine Fin.cases ?_ (fun i' => ?_) i
      · rw [Finset.sum_eq_single (0 : Fin (N + 2))]
        · refine Fin.cases ?_ (fun j' => ?_) j
          · simp [lowerBidiag, elemSubdiag0]
          · have hne : (0 : Fin (N + 2)) ≠ j'.succ := (Fin.succ_ne_zero j').symm
            simp [lowerBidiag, elemSubdiag0, hne]
        · intro k _ hk
          have hE : elemSubdiag0 N (d 0) 0 k = 0 := by
            simp [elemSubdiag0, Ne.symm hk]
          rw [hE, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · refine Fin.cases ?_ (fun i'' => ?_) i'
        · -- Row 1 = `(0 : Fin (N + 1)).succ`
          rw [Fin.sum_univ_succ]
          have hE10 : elemSubdiag0 N (d 0) (0 : Fin (N + 1)).succ 0 = d 0 := by
            simp [elemSubdiag0]
          have hrest :
              (∑ k : Fin (N + 1),
                elemSubdiag0 N (d 0) (0 : Fin (N + 1)).succ k.succ *
                  blockDiagOne (lowerBidiag N (fun r => d r.succ)) k.succ j) =
                blockDiagOne (lowerBidiag N (fun r => d r.succ)) (0 : Fin (N + 1)).succ j := by
            rw [Finset.sum_eq_single (0 : Fin (N + 1))]
            · have hE11 : elemSubdiag0 N (d 0) (0 : Fin (N + 1)).succ (0 : Fin (N + 1)).succ = 1 := by
                simp [elemSubdiag0]
              rw [hE11, one_mul]
            · intro k _ hk
              have hne : (1 : Fin (N + 2)) ≠ k.succ := by
                rw [← Fin.succ_zero_eq_one]
                exact fun h => hk (Fin.succ_injective _ h).symm
              have hE : elemSubdiag0 N (d 0) (0 : Fin (N + 1)).succ k.succ = 0 := by
                simp [elemSubdiag0, hne]
              rw [hE, zero_mul]
            · intro h; exact absurd (Finset.mem_univ _) h
          rw [hE10, hrest]
          refine Fin.cases ?_ (fun j' => ?_) j
          · rw [blockDiagOne_zero_zero, blockDiagOne_succ_zero]
            simp [lowerBidiag]
          · refine Fin.cases ?_ (fun j'' => ?_) j'
            · rw [blockDiagOne_zero_succ, blockDiagOne_succ_succ]
              simp [lowerBidiag]
            · rw [blockDiagOne_zero_succ, blockDiagOne_succ_succ]
              have hne1 : (1 : Fin (N + 2)) ≠ j''.succ.succ := by
                intro h
                have hv := congrArg Fin.val h
                simp only [Fin.val_one, Fin.val_succ] at hv
                omega
              have hne2 : (0 : Fin (N + 1)) ≠ j''.succ := (Fin.succ_ne_zero j'').symm
              simp [lowerBidiag, hne1, hne2]
        · -- Row `i'' + 2`
          rw [Finset.sum_eq_single i''.succ.succ]
          · have hE : elemSubdiag0 N (d 0) i''.succ.succ i''.succ.succ = 1 := by
              simp [elemSubdiag0]
            rw [hE, one_mul]
            refine Fin.cases ?_ (fun j' => ?_) j
            · rw [blockDiagOne_succ_zero]
              simp [lowerBidiag]
            · rw [blockDiagOne_succ_succ]
              simp only [lowerBidiag, Fin.succ_inj, Fin.val_succ, add_left_inj]
              by_cases hij : i''.succ = j'
              · simp [hij]
              · simp only [hij, ite_false]
                split_ifs with h1
                · rfl
                · rfl
          · intro k _ hk
            have hE : elemSubdiag0 N (d 0) i''.succ.succ k = 0 := by
              have hne : i''.succ.succ ≠ k := hk.symm
              simp [elemSubdiag0, hne]
            rw [hE, zero_mul]
          · intro h; exact absurd (Finset.mem_univ _) h
    rw [hfac]
    exact isTotallyNonneg_mul (elemSubdiag0_isTotallyNonneg N (hd 0))
      (isTotallyNonneg_blockDiagOne (ih (fun r => hd r.succ)))

end Conjectures.WangYangFussNarayana
