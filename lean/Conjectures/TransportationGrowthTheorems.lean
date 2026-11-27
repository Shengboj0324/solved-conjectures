import Conjectures.TransportationLatticeHull
import Conjectures.TransportationNonrealGrowth

/-! The growing nonreal-root count holds for the uniquely characterized
Ehrhart numerator of the full-support lattice polytopes themselves. -/

namespace TransportationEhrhart

open Filter

theorem family_nonreal_growth : ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
    (∃ a∈polytope n,∀ i j,0<a i j) ∧
    Module.finrank ℝ (vectorSpan ℝ (polytope n))=2*n ∧
    (∃ p : Polynomial ℝ,IsEhrhartNumerator n p) ∧
    ∀ p : Polynomial ℝ,IsEhrhartNumerator n p →
      c*Real.sqrt ((n : ℝ)*Real.log n)≤((nonrealRoots p).card : ℝ) := by
  obtain ⟨c,cp,h⟩ := eventual_nonreal_growth
  refine ⟨c,cp,?_⟩
  filter_upwards [h,eventually_ge_atTop 2] with n hn n2
  have pos : 0<n := by omega
  refine ⟨every_cell_positive pos,affine_dimension n,⟨numerator n,(numerator_characterization pos _).2 rfl⟩,?_⟩
  intro p hp
  simpa only [(numerator_characterization pos p).1 hp] using hn

end TransportationEhrhart
