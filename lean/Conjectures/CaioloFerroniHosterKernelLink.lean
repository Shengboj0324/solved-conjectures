import Conjectures.CaioloFerroniHoster
import Conjectures.CaioloFerroniHosterRanks

/-!
# The rank-five counterexample at the level of the CFH kernel definitions

`counterexample_family` is stated for `matroidDualChow` and `matroidDualAugmented`, the
rank-five chain expansions of CFH Propositions 4.6–4.7 (arXiv:2605.28474v1). The rank-threshold
development defines the same invariants recursively (`Ranks.dualChow`, `Ranks.dualAug`) and
identifies them with the kernel definitions of the paper (`Ranks.dualChow_eq_kernel`,
`Ranks.dualAug_eq_kernel`).

This file proves that the two formulas agree for every rank-five matroid on a finite projective
point type (`matroidDualChow_eq`, `matroidDualAugmented_eq`). Consequently the explicit bound
`17 ≤ q` of `counterexample_family` holds for the kernel-defined functions
(`counterexample_family_kernel`), and not only the unspecified bound of `Ranks.counterexamples`.

The rank-five counterexample is due to Cinna Davis; the coalescence method is due to
Bérczi–Coron–Eur–Li (arXiv:2610.17135v1).
-/

set_option linter.unusedSectionVars false

namespace CaioloFerroniHoster.KernelLink

open Finset Polynomial
open scoped Classical BigOperators

noncomputable section

/-- Inclusion–exclusion over the first rank of a list. -/
theorem beta_cons {A : Type*} [Ring A] (g : List ℕ → A) (m : ℕ) (t : List ℕ) :
    CaioloFerroniHoster.beta g (m :: t) =
      CaioloFerroniHoster.beta (fun s => g (m :: s)) t - CaioloFerroniHoster.beta g t := by
  simp only [CaioloFerroniHoster.beta, signedSublists, List.map_append, List.map_map,
    List.sum_append, Function.comp_def, Int.cast_neg, neg_mul, sub_eq_add_neg]
  congr 1
  induction signedSublists t with
  | nil => simp
  | cons p ps ih => simp [ih]; abel

/-- The inclusion–exclusion transform is additive in the flag function. -/
theorem beta_sum {A ι : Type*} [CommRing A] (s : Finset ι) (g : ι → List ℕ → A) (t : List ℕ) :
    CaioloFerroniHoster.beta (fun l => ∑ i ∈ s, g i l) t =
      ∑ i ∈ s, CaioloFerroniHoster.beta (g i) t := by
  simp only [CaioloFerroniHoster.beta, Finset.mul_sum]
  induction signedSublists t with
  | nil => simp
  | cons p ps ih => simp [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- Ring homomorphisms commute with the inclusion–exclusion transform. -/
theorem beta_map {A B : Type*} [Ring A] [Ring B] (φ : A →+* B) (g : List ℕ → A) (t : List ℕ) :
    CaioloFerroniHoster.beta (fun l => φ (g l)) t = φ (CaioloFerroniHoster.beta g t) := by
  simp only [CaioloFerroniHoster.beta, map_list_sum, List.map_map, Function.comp_def, map_mul,
    map_intCast]

section Signed

variable {P : Type*} [Fintype P] [PartialOrder P] [OrderBot P]

/-- The recursive flag h-numbers of the rank development are the inclusion–exclusion transform,
used in the rank-five arithmetic, of the flag counts. -/
theorem beta_eq_signed (ρ : P → ℕ) :
    ∀ (l : List ℕ) (x : P),
      Ranks.beta ρ x l = CaioloFerroniHoster.beta (Ranks.alpha ρ x) l
  | [], x => by simp [Ranks.beta, CaioloFerroniHoster.beta, signedSublists, Ranks.alpha]
  | m :: t, x => by
      rw [Ranks.beta, beta_cons, Finset.sum_congr rfl fun y _ => beta_eq_signed ρ t y,
        beta_eq_signed ρ t x, ← beta_sum]
      rfl

end Signed

section RankFive

variable {F₀ V X : Type} [Field F₀] [Fintype F₀] [AddCommGroup V] [Module F₀ V]
  [Module.Finite F₀ V] [Finite V] [Finite X] [Finite (Point F₀ V X)]

theorem stab_four : Ranks.stab 4 =
    [([4, 3, 2, 1], 0), ([4, 3, 2], 1), ([4, 3, 1], 1), ([4, 2, 1], 1), ([4, 2], 2)] := by
  decide

theorem stab_three : Ranks.stab 3 = [([3, 2, 1], 0), ([3, 2], 1), ([3, 1], 1)] := by
  decide

/-- Flag counts of the explicit flag types agree with those of the lattice of flats. -/
theorem matroidFlag_eq (M : Matroid (Point F₀ V X)) (s : List ℕ) :
    matroidFlag M s = (Ranks.alpha (Ranks.flatRk M) (⊤ : Ranks.Flats M) s : ℝ) := by
  rw [Ranks.alpha_eq_card (F := F₀) M s ⊤, matroidFlag]
  rfl

/-- For a rank-five matroid, the chain-formula dual Chow polynomial used in
`counterexample_family` is the dual Chow polynomial of the rank development. -/
theorem matroidDualChow_eq (M : Matroid (Point F₀ V X)) (h5 : M.eRank = 5) : matroidDualChow M = Ranks.realChow M := by
  have hf : (fun s => C (matroidFlag M s)) =
      fun s => (Polynomial.C.comp (Int.castRingHom ℝ)) (Ranks.alpha (Ranks.flatRk M) ⊤ s) := by
    funext s; simp [matroidFlag_eq M]
  rw [matroidDualChow, dualChow_gamma, hf, Ranks.realChow, Ranks.dualChow_eq M (n := 4) h5,
    Ranks.gammaSum, stab_four]
  simp only [gammaZero, gammaOne, gammaTwo, beta_map, ← beta_eq_signed]
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
  ring

/-- For a rank-five matroid, the chain-formula dual right augmented polynomial used in
`counterexample_family` is the dual right augmented polynomial of the rank development. -/
theorem matroidDualAugmented_eq (M : Matroid (Point F₀ V X)) (h5 : M.eRank = 5) : matroidDualAugmented M = Ranks.realAug M := by
  have hf : (fun s => C (matroidFlag M s)) =
      fun s => (Polynomial.C.comp (Int.castRingHom ℝ)) (Ranks.alpha (Ranks.flatRk M) ⊤ s) := by
    funext s; simp [matroidFlag_eq M]
  rw [matroidDualAugmented, dualRightAugmented_gamma, hf, Ranks.realAug,
    Ranks.dualAug_eq M (n := 4) h5, Ranks.gammaSumAug, Ranks.gammaSum, Ranks.gammaSum,
    stab_four, stab_three]
  simp only [gammaZero, gammaOne, gammaTwo, gammaOneAug, gammaTwoAug, beta_map, ← beta_eq_signed]
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
  ring

end RankFive

/-- **Kernel-level form of the main theorem.** For every prime power `q ≥ 17` there is a simple
rank-five matroid whose dual Chow function and dual right augmented Chow function, defined by the
CFH kernel equations (Definitions 2.4, 2.7, 2.8, 3.1 and Theorem 2.3), have the root properties of
`counterexample_family`. In particular neither top polynomial is real-rooted. -/
theorem counterexample_family_kernel (q : ℕ) (hprime : IsPrimePow q) (hq : 17 ≤ q) :
    ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Fintype F) (_ : Fintype K)
      (_ : Algebra F K), Fintype.card F = q ∧ Module.finrank F K = 4 ∧
      ∃ M : Matroid (Point F (K × K) K),
        M.E = Set.univ ∧ IsSimple M ∧ M.eRank = 5 ∧
        ∀ H f : Ranks.Flats M → Ranks.Flats M → ℤ[X],
          Ranks.IsChow (Ranks.dualKernel (Ranks.flatRk M)) H →
          Ranks.IsRightKLS (Ranks.flatRk M) (Ranks.dualKernel (Ranks.flatRk M)) f →
          ((H ⊥ ⊤).map (Int.castRingHom ℝ)).natDegree = 4 ∧
          (∀ x : ℝ, 0 < ((H ⊥ ⊤).map (Int.castRingHom ℝ)).eval x) ∧
          ((Ranks.conv H (Ranks.revF (Ranks.flatRk M) f) ⊥ ⊤).map
            (Int.castRingHom ℝ)).natDegree = 5 ∧
          (∀ x : ℝ, ((Ranks.conv H (Ranks.revF (Ranks.flatRk M) f) ⊥ ⊤).map
            (Int.castRingHom ℝ)).eval x = 0 ↔ x = -1) ∧
          ((Ranks.conv H (Ranks.revF (Ranks.flatRk M) f) ⊥ ⊤).map
            (Int.castRingHom ℝ)).derivative.eval (-1) ≠ 0 ∧
          ¬ ((H ⊥ ⊤).map (Int.castRingHom ℝ)).Splits ∧
          ¬ ((Ranks.conv H (Ranks.revF (Ranks.flatRk M) f) ⊥ ⊤).map
            (Int.castRingHom ℝ)).Splits := by
  obtain ⟨F, K, iF, iK, fF, fK, iA, hF, hK, M, hE, hS, h5, d1, p1, d2, r2, s2, n1, n2⟩ :=
    counterexample_family q hprime hq
  refine ⟨F, K, iF, iK, fF, fK, iA, hF, hK, M, hE, hS, h5, fun H f hH hf => ?_⟩
  have eH : (H ⊥ ⊤).map (Int.castRingHom ℝ) = matroidDualChow M := by
    rw [Ranks.dualChow_eq_kernel M hH, matroidDualChow_eq M h5]
  have eF : (Ranks.conv H (Ranks.revF (Ranks.flatRk M) f) ⊥ ⊤).map (Int.castRingHom ℝ) =
      matroidDualAugmented M := by
    rw [Ranks.dualAug_eq_kernel M hH hf, matroidDualAugmented_eq M h5]
  rw [eH, eF]
  exact ⟨d1, p1, d2, r2, s2, n1, n2⟩

end
end CaioloFerroniHoster.KernelLink
