import Conjectures.ErdosGyarfasSpectrumExtremal
import Conjectures.ErdosGyarfasSpectrumRealDegrees

/-! The original extremal questions, with the real-plane bound also covering
collinear configurations. -/

namespace ErdosGyarfasSpectrum

theorem le_extremal {n : ℕ} {lines : Finset (Finset (Fin n))} (space : LinearOn Finset.univ lines) :
    (degrees Finset.univ lines).card≤extremal n := Finset.le_sup (f := fun l => (degrees Finset.univ l).card)
      (mem_systems.mpr space)

theorem eventually_linear_deficit (C : ℝ) : ∃ N : ℕ, ∀ n≥N,
    C*Real.sqrt n < (n : ℝ)-extremal n := by
  obtain ⟨k,hk⟩ := exists_nat_gt ((17*C)^2)
  refine ⟨max 3 k,fun n hn => no_sqrt_deficit C (by omega) ?_⟩
  exact hk.trans_le (by exact_mod_cast (show k≤n by omega))

theorem no_near_full_spectrum :
    ¬∃ (C : ℝ) (N : ℕ), ∀ n≥N,(n : ℝ)-C*Real.sqrt n ≤ extremal n := by
  rintro ⟨C,N,h⟩
  obtain ⟨K,hK⟩ := eventually_linear_deficit C
  have a := h (max N K) (le_max_left _ _)
  have b := hK (max N K) (le_max_right _ _)
  linarith

theorem collinear_degree_one {P : Finset PlanePoint} (col : Collinear ℝ (P : Set PlanePoint))
    (hn : 2≤P.card) {p : PlanePoint} (hp : p∈P) : (GyarfasPlanar.spannedLines P p).card=1 := by
  classical
  have size := Finset.card_erase_add_one hp
  obtain ⟨q,hq⟩ := Finset.card_pos.mp (show 0<(P.erase p).card by omega)
  have val {r : PlanePoint} (hr : r∈P.erase p) :
      lineSet p r=(affineSpan ℝ (P : Set PlanePoint) : Set PlanePoint) := by
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hr
    exact congrArg SetLike.coe (col.affineSpan_eq_of_ne hp mem ne.symm)
  have eq : GyarfasPlanar.spannedLines P p={(affineSpan ℝ (P : Set PlanePoint) : Set PlanePoint)} := by
    ext L
    constructor
    · intro hL
      obtain ⟨r,hr,eq⟩ := Finset.mem_image.mp hL
      exact Finset.mem_singleton.mpr (eq.symm.trans (val hr))
    · intro hL
      obtain rfl := Finset.mem_singleton.mp hL
      exact Finset.mem_image.mpr ⟨q,hq,val hq⟩
  rw [eq,Finset.card_singleton]

theorem real_positive_proportion (P : Finset PlanePoint) (hn : 3≤P.card) :
    17*(P.image (fun p => (GyarfasPlanar.spannedLines P p).card)).card+13 ≤ 16*P.card := by
  by_cases col : Collinear ℝ (P : Set PlanePoint)
  · have inc : P.image (fun p => (GyarfasPlanar.spannedLines P p).card)⊆({1} : Finset ℕ) := by
      intro d hd
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
      exact Finset.mem_singleton.mpr (collinear_degree_one col (by omega) hp)
    have card := Finset.card_le_card inc
    rw [Finset.card_singleton] at card
    omega
  · exact real_degree_bound P col

end ErdosGyarfasSpectrum
