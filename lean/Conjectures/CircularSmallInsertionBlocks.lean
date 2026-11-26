import Conjectures.CircularSmallInsertionFamily
import Conjectures.CircularSmallInsertionExclusions

/-! The three actual colour supports in a forward insertion are pairwise
disjoint, including at wraparound. This also applies to each positive witness. -/

namespace CircularIndex.Insertion.Small

private theorem window_order {g k c i j : ℕ} (hk₁ : 1≤k) (hk₂ : k≤2*g)
    (hi : i<j) (hj : j<3) (v : ℕ) (h : v∈classSupport g k (colour g c i)) :
    v∉classSupport g k (colour g c j) := by
  have eq : colour g (colour g c i) (j-i)=colour g c j := by
    unfold colour
    rw [Nat.mod_add_mod]
    congr 1
    omega
  rw [←eq]
  exact general_window hk₁ hk₂ (show j-i=1 ∨ j-i=2 by omega) v h

theorem block_supports_disjoint {g k : ℕ} (hk₁ : 1≤k) (hk₂ : k≤2*g)
    (c : ℕ) (i j : Fin 3) (neq : i≠j) (v : ℕ) :
    v∈classSupport g k (colour g c i.val) → v∉classSupport g k (colour g c j.val) := by
  intro h h'
  have diff : i.val≠j.val := fun eq => neq (Fin.ext eq)
  rcases (show i.val<j.val ∨ j.val<i.val by omega) with lt|gt
  · exact window_order hk₁ hk₂ lt j.isLt v h h'
  · exact window_order hk₁ hk₂ gt i.isLt v h' h

theorem feasible_five_with_disjoint_classes {k : ℕ} (hk₁ : 1≤k) (hk₂ : k<10) (c : ℕ) :
    (OneForward 5 k c ∧ ∀ i j : Fin 3, i≠j → ∀ v,
      v∈classSupport 5 k (colour 5 c i.val) → v∉classSupport 5 k (colour 5 c j.val)) ↔
      k=2 ∨ k=8 := by
  exact ⟨fun h => (forward_five_iff hk₁ hk₂ c).mp h.1,fun h =>
    ⟨(forward_five_iff hk₁ hk₂ c).mpr h,block_supports_disjoint hk₁ (by omega) c⟩⟩

end CircularIndex.Insertion.Small
