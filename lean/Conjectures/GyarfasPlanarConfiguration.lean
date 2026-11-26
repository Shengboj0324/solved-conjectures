import Conjectures.GyarfasPlanarSecants

/-! The axis heights are indexed without duplication, including the replaced
height 1 and the extra height −1 at odd orders. -/

namespace GyarfasPlanar

def slotHeight (k i : ℕ) : ℤ := if i=1 then 2*(k : ℤ)-3 else if i=k then -1 else i

theorem heights_mem (k : ℕ) (odd : Bool) (s : ℤ) :
    s∈heights k odd ↔ s=2*(k : ℤ)-3 ∨ (s≠1 ∧ 0≤s ∧ s<k) ∨ (odd=true ∧ s= -1) := by
  have ints : s∈(Finset.range k).image Int.ofNat ↔ 0≤s ∧ s<k := by
    constructor
    · intro h
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
      have := Finset.mem_range.mp hj
      change 0≤(j : ℤ) ∧ (j : ℤ)<k
      omega
    · intro h
      exact Finset.mem_image.mpr ⟨s.toNat,Finset.mem_range.mpr (by omega),by change (s.toNat : ℤ)=s; omega⟩
  cases odd
  · simp [heights,ints]
  · simp [heights,ints]
    tauto

theorem slot_injective {k : ℕ} (hk : 8≤k) (odd : Bool) {i j : ℕ}
    (hi : i<k+odd.toNat) (hj : j<k+odd.toNat) (h : slotHeight k i=slotHeight k j) : i=j := by
  unfold slotHeight at h
  cases odd <;> simp only [Bool.toNat_false,Bool.toNat_true] at hi hj <;> split_ifs at h <;> omega

theorem heights_as_slots {k : ℕ} (hk : 8≤k) (odd : Bool) :
    heights k odd=(Finset.range (k+odd.toNat)).image (slotHeight k) := by
  ext s
  rw [heights_mem,Finset.mem_image]
  constructor
  · rintro (rfl|⟨hs,h₀,hk'⟩|⟨rfl,rfl⟩)
    · exact ⟨1,Finset.mem_range.mpr (by omega),by simp [slotHeight]⟩
    · refine ⟨s.toNat,Finset.mem_range.mpr (by omega),?_⟩
      have h₁ : s.toNat≠1 := by omega
      have h₂ : s.toNat≠k := by omega
      simpa [slotHeight,h₁,h₂] using (show (s.toNat : ℤ)=s by omega)
    · exact ⟨k,by simp,by simp [slotHeight,show k≠1 by omega]⟩
  · rintro ⟨i,hi,rfl⟩
    have hi' := Finset.mem_range.mp hi
    by_cases h₁ : i=1
    · exact Or.inl (by simp [slotHeight,h₁])
    by_cases h₂ : i=k
    · have he : odd=true := by
        cases odd
        · simp [h₂] at hi'
        · rfl
      exact Or.inr (Or.inr ⟨he,by simp only [slotHeight,ite_eq_right h₁,ite_eq_left h₂]⟩)
    · apply Or.inr (Or.inl ?_)
      simp only [slotHeight,ite_eq_right h₁,ite_eq_right h₂]
      cases odd <;> simp at hi' <;> omega

theorem heights_card {k : ℕ} (hk : 8≤k) (odd : Bool) : (heights k odd).card=k+odd.toNat := by
  rw [heights_as_slots hk,Finset.card_image_of_injOn,Finset.card_range]
  intro i hi j hj eq
  exact slot_injective hk odd (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) eq

theorem configuration_card {k : ℕ} (hk : 8≤k) (odd : Bool) :
    (configuration k odd).card=2*k+odd.toNat := by
  have dis : Disjoint ((Finset.range k).image offAxis) ((heights k odd).image onAxis) := by
    apply Finset.disjoint_left.mpr
    intro p hp hs
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨s,_,eq⟩ := Finset.mem_image.mp hs
    exact off_ne_on i s eq.symm
  rw [configuration,Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ off_injective,
    Finset.card_image_of_injective _ on_injective,Finset.card_range,heights_card hk]
  omega

theorem configuration_noncollinear {k : ℕ} (hk : 8≤k) (odd : Bool) :
    ¬Collinear ℝ (↑((configuration k odd).image realPoint) : Set (Point ℝ)) := by
  have axis (s : ℤ) (hs : s∈heights k odd) : onAxis s∈configuration k odd :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)
  apply axis_triangle_noncollinear
  · exact axis 0 ((heights_mem ..).mpr (Or.inr (Or.inl ⟨by decide,by decide,by omega⟩)))
  · exact axis 2 ((heights_mem ..).mpr (Or.inr (Or.inl ⟨by decide,by decide,by omega⟩)))
  · have h : offAxis 0∈configuration k odd := Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))
    simpa [offAxis] using h

end GyarfasPlanar
