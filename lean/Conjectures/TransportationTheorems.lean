import Conjectures.TransportationVertices
import Conjectures.TransportationComplexRoots

/-! The Ehrhart numerator is characterized by the integer points of the
dilated polytope and its actual affine dimension. -/

namespace TransportationEhrhart

def IsEhrhartNumerator (m : ℕ) (h : Polynomial ℝ) : Prop :=
  ehrhartSeries m*(1-PowerSeries.X)^(Module.finrank ℝ (vectorSpan ℝ (polytope m))+1)=(h : PowerSeries ℝ)

theorem numerator_characterization {m : ℕ} (hm : 0<m) (p : Polynomial ℝ) :
    IsEhrhartNumerator m p ↔ p=numerator m := by
  unfold IsEhrhartNumerator
  rw [affine_dimension,integer_points_numerator hm]
  constructor
  · intro h
    exact Polynomial.coe_injective ℝ h.symm
  · rintro rfl
    rfl

theorem transportation_counterexample :
    (∃ i : Fin 3,1<rowMargin 12 1 i) ∧ (∃ j : Col 12,1<capacity 1 j) ∧
    (∃ a∈polytope 12,∀ i j,0<a i j) ∧
    Fintype.card (Fin 3 × Col 12)=39 ∧ Module.finrank ℝ (vectorSpan ℝ (polytope 12))=24 ∧
    ∃ h : Polynomial ℝ,IsEhrhartNumerator 12 h ∧ ¬h.Splits ∧ h.natDegree=12 ∧
      h.roots.card=10 ∧ h.roots.toFinset.card=10 ∧ (nonrealRoots h).card=2 := by
  refine ⟨⟨2,by decide⟩,⟨none,by decide⟩,every_cell_positive (by decide),?_,affine_dimension 12,
    numerator 12,(numerator_characterization (by decide) _).mpr rfl,twelve_not_real_rooted,
    twelve_degree,twelve_real_roots.1,twelve_real_roots.2,twelve_nonreal_roots⟩
  simp [Col,Fintype.card_prod]

end TransportationEhrhart
