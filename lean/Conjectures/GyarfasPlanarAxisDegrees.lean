import Conjectures.GyarfasPlanarDirections
import Mathlib.Order.Interval.Finset.Nat

/-! The on-axis degree equals k+1 minus the number of unordered pairs of
off-axis indices summing to the height. These pairs have disjoint endpoints. -/

namespace GyarfasPlanar

private def representatives (k a : ℕ) := Finset.range (a/2+1) ∪ Finset.Ico (a+1) k

private theorem rep_mem (k a i : ℕ) : i ∈ representatives k a ↔ i < a / 2 + 1 ∨ (a + 1 ≤ i ∧ i < k) := by
  simp [representatives]

private theorem below_axis_values {k a : ℕ} (ha : a<k) :
    axisValues k a=(representatives k a).image (fun i => axisSlope i a) := by
  ext m
  constructor
  · intro hm
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hm
    have hi' := Finset.mem_range.mp hi
    by_cases good : i∈representatives k a
    · exact Finset.mem_image_of_mem _ good
    · have bad := (rep_mem k a i).not.mp good
      refine Finset.mem_image.mpr ⟨a-i,(rep_mem ..).mpr (Or.inl (by omega)),?_⟩
      exact (axis_collisions ..).mpr (Or.inr (by omega))
  · intro hm
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hm
    have h := (rep_mem ..).mp hi
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))

theorem axis_value_count_low {k a : ℕ} (ha : a<k) :
    (axisValues k a).card=k-(a+1)/2 := by
  have inj : Set.InjOn (fun i => axisSlope i a) (↑(representatives k a) : Set ℕ) := by
    intro i hi j hj eq
    have h₁ := (rep_mem ..).mp hi
    have h₂ := (rep_mem ..).mp hj
    rcases (axis_collisions ..).mp eq with same|sum <;> omega
  have dis : Disjoint (Finset.range (a/2+1)) (Finset.Ico (a+1) k) := by
    apply Finset.disjoint_left.mpr
    intro i h₁ h₂
    have := Finset.mem_range.mp h₁
    have := Finset.mem_Ico.mp h₂
    omega
  rw [below_axis_values ha,Finset.card_image_of_injOn inj,representatives,Finset.card_union_of_disjoint dis,
    Finset.card_range,Nat.card_Ico]
  omega

theorem axis_value_count_extra (k : ℕ) : (axisValues k (-1)).card=k := by
  rw [axisValues,Finset.card_image_of_injOn,Finset.card_range]
  intro i _ j _ eq
  rcases (axis_collisions ..).mp eq with h|h <;> omega

theorem axis_value_count_high {k : ℕ} (hk : 8≤k) : (axisValues k (2*(k : ℤ)-3)).card=k-1 := by
  let slope (i : ℕ) := axisSlope i (2*(k : ℤ)-3)
  have eq : axisValues k (2*(k : ℤ)-3)=(Finset.range (k-1)).image slope := by
    ext m
    constructor
    · intro hm
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hm
      have hi' := Finset.mem_range.mp hi
      by_cases h : i<k-1
      · exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr h)
      · exact Finset.mem_image.mpr ⟨k-2,Finset.mem_range.mpr (by omega),
          (axis_collisions ..).mpr (Or.inr (by omega))⟩
    · intro hm
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hm
      have := Finset.mem_range.mp hi
      exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))
  rw [eq,Finset.card_image_of_injOn,Finset.card_range]
  intro i hi j hj he
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  rcases (axis_collisions ..).mp he with h|h <;> omega

def axisDegree (k i : ℕ) := if i=k then k+1 else k+1-(i+1)/2

theorem axis_degree {k i : ℕ} (hk : 8≤k) (odd : Bool) (hi : i<k+odd.toNat) :
    (directions (configuration k odd) (onAxis (slotHeight k i))).card=axisDegree k i := by
  rw [axis_degree_eq hk]
  by_cases one : i=1
  · subst i
    rw [slotHeight,ite_eq_left rfl,axis_value_count_high hk]
    unfold axisDegree
    split <;> omega
  by_cases last : i=k
  · rw [slotHeight,ite_eq_right one,ite_eq_left last,axis_value_count_extra,axisDegree,ite_eq_left last]
  · have low : i<k := by cases odd <;> simp at hi <;> omega
    rw [slotHeight,ite_eq_right one,ite_eq_right last,axis_value_count_low low,axisDegree,ite_eq_right last]
    omega

end GyarfasPlanar
