import Conjectures.ErdosGyarfasSpectrumBound
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-! The extremal function really is an attained maximum over all labelled
linear spaces, and its deficit eventually exceeds every constant times √n. -/

namespace ErdosGyarfasSpectrum

def pairs (n : ℕ) := (Finset.univ : Finset (Fin n)).powersetCard 2

theorem pair_space {n : ℕ} (hn : 3≤n) : LinearOn Finset.univ (pairs n) := by
  classical
  refine ⟨by simpa,fun _ _ => Finset.subset_univ _,?_,?_⟩
  · intro l hl
    have c := (Finset.mem_powersetCard.mp hl).2
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  · intro p _ q _ ne
    have card := Finset.card_pair ne
    refine ⟨{p,q},⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,card⟩,by simp,by simp⟩,?_⟩
    rintro l ⟨hl,hp,hq⟩
    have inc : ({p,q} : Finset (Fin n))⊆l := Finset.insert_subset_iff.mpr ⟨hp,Finset.singleton_subset_iff.mpr hq⟩
    have count := (Finset.mem_powersetCard.mp hl).2
    exact (Finset.eq_of_subset_of_card_le inc (by omega)).symm

noncomputable def systems (n : ℕ) : Finset (Finset (Finset (Fin n))) := by
  classical
  exact Finset.univ.filter fun lines => LinearOn Finset.univ lines

theorem mem_systems {n : ℕ} {lines : Finset (Finset (Fin n))} :
    lines∈systems n ↔ LinearOn Finset.univ lines := by classical exact (by simp [systems])

noncomputable def extremal (n : ℕ) : ℕ :=
  (systems n).sup fun lines => (degrees Finset.univ lines).card

theorem extremal_attained {n : ℕ} (hn : 3≤n) :
    ∃ lines : Finset (Finset (Fin n)), LinearOn Finset.univ lines ∧
      extremal n=(degrees Finset.univ lines).card := by
  have nonempty : (systems n).Nonempty := ⟨pairs n,mem_systems.mpr (pair_space hn)⟩
  obtain ⟨lines,hl,eq⟩ := Finset.exists_mem_eq_sup (systems n) nonempty (fun l => (degrees Finset.univ l).card)
  exact ⟨lines,mem_systems.mp hl,eq⟩

theorem extremal_bound {n : ℕ} (hn : 3≤n) : 17*extremal n+13 ≤ 16*n := by
  obtain ⟨lines,space,eq⟩ := extremal_attained hn
  simpa [eq] using spectrum_bound space

theorem no_sqrt_deficit (C : ℝ) {n : ℕ} (hn : 3≤n) (large : (17*C)^2<(n : ℝ)) :
    C*Real.sqrt n < (n : ℝ)-extremal n := by
  have b : 17*(extremal n : ℝ)+13 ≤ 16*n := by exact_mod_cast extremal_bound hn
  have sn := Real.sqrt_nonneg (n : ℝ)
  have sq := Real.sq_sqrt (show 0≤(n : ℝ) by positivity)
  have sp : 0<Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))
  have less : 17*C < Real.sqrt n := by
    by_contra! rev
    have b' := mul_self_le_mul_self sn rev
    nlinarith
  have mult := mul_lt_mul_of_pos_right less sp
  nlinarith only [b,sq,mult]

theorem comparison_sqrt {V : Type*} [DecidableEq V] {P X Y : Finset V} {lines : Finset (Finset V)}
    (space : LinearOn P lines) (hX : X⊆P) (hY : Y⊆P) (disj : Disjoint X Y)
    {t : ℕ} (hx : X.card=t) (hy : Y.card=t) :
    let A : ℝ := lowTotal lines X
    let S : ℝ := A+highTotal P lines Y-(t : ℝ)^2
    0≤S ∧ (t : ℝ)^2-A ≤ Real.sqrt (((t : ℝ)*(t-1)+S)*S) := by
  obtain ⟨hs,C,_,lo,hi⟩ := two_set_comparison space hX hY disj hx hy
  dsimp only
  refine ⟨by exact_mod_cast hs,?_⟩
  have low : (t : ℝ)^2-lowTotal lines X ≤ C := by exact_mod_cast lo
  exact low.trans (Real.le_sqrt_of_sq_le (by exact_mod_cast hi))

end ErdosGyarfasSpectrum
