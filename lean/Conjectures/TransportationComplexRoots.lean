import Conjectures.TransportationTwelveRoots
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Count the complex roots whose imaginary part is nonzero, with multiplicity. -/

namespace TransportationEhrhart

open Polynomial

noncomputable def nonrealRoots (p : ℝ[X]) : Multiset ℂ := by
  classical exact (p.map Complex.ofRealHom).roots.filter (fun z => z.im ≠ 0)

theorem complex_root_accounting (p : ℝ[X]) : p.roots.card+(nonrealRoots p).card=p.natDegree := by
  classical
  let f := Complex.ofRealHom
  have range_eq (z : ℂ) : z ∈ f.range ↔ z.im=0 := by
    constructor
    · rintro ⟨x,rfl⟩
      rfl
    · intro h
      refine ⟨z.re,Complex.ext rfl ?_⟩
      exact h.symm
  have partition := congrArg Multiset.card (Multiset.filter_add_not (fun z : ℂ => z ∈ f.range) (p.map f).roots)
  rw [Multiset.card_add,filter_roots_map_range_eq_map_roots (f := f) Complex.ofReal_injective,
    Multiset.card_map] at partition
  simp only [range_eq] at partition
  have total := (IsAlgClosed.splits (p.map f)).natDegree_eq_card_roots
  rw [p.natDegree_map_eq_of_injective Complex.ofReal_injective] at total
  exact partition.trans total.symm

theorem twelve_nonreal_roots : (nonrealRoots (numerator 12)).card=2 := by
  have h := complex_root_accounting (numerator 12)
  rw [twelve_real_roots.1,twelve_degree] at h
  omega

end TransportationEhrhart
