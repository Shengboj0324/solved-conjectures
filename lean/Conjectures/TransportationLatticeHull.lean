import Conjectures.TransportationSlots
import Conjectures.TransportationTheorems

/-! The integral generators of the real polytope are grouped permutation
matrices. This supplies the lattice-polytope hypothesis as well as the explicit
39-cell counterexample. -/

namespace TransportationEhrhart

def permutationTable (m : ℕ) (σ : Equiv.Perm (Slot m)) : Fin 3 → Col m → ℕ :=
  grouped slotRow slotColumn (σ.permMatrix ℕ)

theorem permutation_cast {ι : Type*} [DecidableEq ι] (σ : Equiv.Perm ι) (i j : ι) :
    σ.permMatrix ℝ i j=(σ.permMatrix ℕ i j : ℝ) := by
  simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply]
  split <;> norm_num

theorem integral_generator (m : ℕ) (σ : Equiv.Perm (Slot m)) :
    grouping slotRow slotColumn (σ.permMatrix ℝ)=fun i j => (permutationTable m σ i j : ℝ) := by
  funext i j
  change (∑ t ∈ fiber slotRow i,∑ s ∈ fiber slotColumn j,σ.permMatrix ℝ t s) =
    ((∑ t ∈ fiber slotRow i,∑ s ∈ fiber slotColumn j,σ.permMatrix ℕ t s : ℕ) : ℝ)
  simp only [Nat.cast_sum,permutation_cast]

theorem finite_integral_hull {m : ℕ} (hm : 0<m) :
    polytope m=convexHull ℝ (Set.range (fun σ : Equiv.Perm (Slot m) =>
      fun i j => (permutationTable m σ i j : ℝ))) := by
  rw [polytope_as_image hm,doublyStochastic_eq_convexHull_permMatrix,LinearMap.image_convexHull]
  congr 1
  change grouping slotRow slotColumn '' Set.range (fun σ : Equiv.Perm (Slot m) => σ.permMatrix ℝ)=_
  rw [← Set.range_comp]
  exact congrArg Set.range (funext (integral_generator m))

theorem integral_hull_counterexample :
    (∃ s : Finset (Fin 3 → Col 12 → ℕ),
      polytope 12=convexHull ℝ ((fun (a : Fin 3 → Col 12 → ℕ) i j => (a i j : ℝ)) '' (s : Set (Fin 3 → Col 12 → ℕ)))) ∧
    (∀ h : Polynomial ℝ, IsEhrhartNumerator 12 h → ¬h.Splits ∧ (nonrealRoots h).card=2) := by
  classical
  constructor
  · refine ⟨Finset.univ.image (permutationTable 12),?_⟩
    rw [finite_integral_hull (by decide : 0<12),Finset.coe_image,Finset.coe_univ,Set.image_univ,← Set.range_comp]
    rfl
  · intro h spec
    rw [(numerator_characterization (by decide) h).mp spec]
    exact ⟨twelve_not_real_rooted,twelve_nonreal_roots⟩

end TransportationEhrhart
