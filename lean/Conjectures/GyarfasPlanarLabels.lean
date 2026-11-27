import Conjectures.GyarfasPlanarAxisDegrees
import Conjectures.GyarfasPlanarOffDegrees

/-! Label the off-axis points first and the axis points second. Both exact
degree formulas then apply to the ordinary index in the complete configuration. -/

namespace GyarfasPlanar

def labelPoint (k t : ℕ) := if t<k then offAxis t else onAxis (slotHeight k (t-k))

def labelDegree (k : ℕ) (odd : Bool) (t : ℕ) :=
  if t<k then offDegree k odd t else axisDegree k (t-k)

theorem configuration_labels {k : ℕ} (hk : 8≤k) (odd : Bool) :
    configuration k odd=(Finset.range (2*k+odd.toNat)).image (labelPoint k) := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with off|axis
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp off
      have h := Finset.mem_range.mp hi
      exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),by simp [labelPoint,h]⟩
    · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp axis
      rw [heights_as_slots hk] at hs
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hs
      have h := Finset.mem_range.mp hj
      exact Finset.mem_image.mpr ⟨k+j,Finset.mem_range.mpr (by omega),
        by simp [labelPoint,show ¬k+j<k by omega]⟩
  · intro hp
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
    have hn := Finset.mem_range.mp ht
    by_cases low : t<k
    · rw [labelPoint,ite_eq_left low]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr low))
    · rw [labelPoint,ite_eq_right low]
      apply Finset.mem_union_right
      apply Finset.mem_image_of_mem
      rw [heights_as_slots hk]
      exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))

theorem label_degree {k t : ℕ} (hk : 8≤k) (odd : Bool) (ht : t<2*k+odd.toNat) :
    (directions (configuration k odd) (labelPoint k t)).card=labelDegree k odd t := by
  by_cases low : t<k
  · simpa only [labelPoint,labelDegree,ite_eq_left low] using off_degree hk low odd
  · simpa only [labelPoint,labelDegree,ite_eq_right low] using
      axis_degree (i := t-k) hk odd (by omega)

theorem label_injective {k i j : ℕ} (hk : 8≤k) (odd : Bool)
    (hi : i<2*k+odd.toNat) (hj : j<2*k+odd.toNat) (eq : labelPoint k i=labelPoint k j) : i=j := by
  by_cases o : i<k <;> by_cases p : j<k
  · exact off_injective (by simpa only [labelPoint,ite_eq_left o,ite_eq_left p] using eq)
  · exact False.elim (off_ne_on i _ (by simpa only [labelPoint,ite_eq_left o,ite_eq_right p] using eq))
  · exact False.elim (off_ne_on j _ (by simpa only [labelPoint,ite_eq_right o,ite_eq_left p] using eq.symm))
  · have es := on_injective (by simpa only [labelPoint,ite_eq_right o,ite_eq_right p] using eq)
    have d := slot_injective hk odd (i := i-k) (j := j-k) (by omega) (by omega) es
    omega

end GyarfasPlanar
