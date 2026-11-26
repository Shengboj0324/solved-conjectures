import Conjectures.GyarfasPlanarConfiguration

/-! Every direction through an off-axis or an on-axis point is accounted for
by the explicit line equations, including the vertical direction on the axis. -/

namespace GyarfasPlanar

def offValues (k : ℕ) (odd : Bool) (i : ℕ) : Finset ℚ :=
  (((Finset.range k).erase i).image (secant i)) ∪ ((heights k odd).image (axisSlope i))

theorem off_directions (k : ℕ) (odd : Bool) (i : ℕ) :
    directions (configuration k odd) (offAxis i)=(offValues k odd i).image some := by
  ext d
  constructor
  · intro h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ne,pt⟩ := Finset.mem_erase.mp hp
    rcases Finset.mem_union.mp pt with m|m
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp m
      have hji : j≠i := fun e => ne (congrArg offAxis e)
      rw [off_secant hji]
      exact Finset.mem_image_of_mem _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _
        (Finset.mem_erase.mpr ⟨hji,hj⟩)))
    · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp m
      rw [direction_swap,axis_secant]
      exact Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs))
  · intro h
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp h
    rcases Finset.mem_union.mp hm with h|h
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨ne,hk⟩ := Finset.mem_erase.mp hj
      apply Finset.mem_image.mpr
      exact ⟨offAxis j,Finset.mem_erase.mpr ⟨fun e => ne (off_injective e),
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ hk)⟩,off_secant ne⟩
    · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp h
      apply Finset.mem_image.mpr
      refine ⟨onAxis s,Finset.mem_erase.mpr ⟨(off_ne_on i s).symm,
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)⟩,?_⟩
      rw [direction_swap,axis_secant]

def axisValues (k : ℕ) (s : ℤ) := (Finset.range k).image (fun i => axisSlope i s)

theorem axis_directions {k : ℕ} (hk : 8≤k) (odd : Bool) (s : ℤ) :
    directions (configuration k odd) (onAxis s)=insert none ((axisValues k s).image some) := by
  have other : ∃ t∈heights k odd, t≠s := by
    by_cases z : s=0
    · exact ⟨2,(heights_mem ..).mpr (Or.inr (Or.inl ⟨by decide,by decide,by omega⟩)),by omega⟩
    · exact ⟨0,(heights_mem ..).mpr (Or.inr (Or.inl ⟨by decide,by decide,by omega⟩)),Ne.symm z⟩
  ext d
  constructor
  · intro h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    rcases Finset.mem_union.mp (Finset.mem_erase.mp hp).2 with m|m
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp m
      rw [axis_secant]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hi))
    · obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp m
      simp [direction,onAxis]
  · intro hd
    rcases Finset.mem_insert.mp hd with rfl|hm
    · obtain ⟨t,ht,ne⟩ := other
      refine Finset.mem_image.mpr ⟨onAxis t,Finset.mem_erase.mpr ⟨fun e => ne (on_injective e),
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht)⟩,?_⟩
      simp [direction,onAxis]
    · obtain ⟨m,member,value⟩ := Finset.mem_image.mp hm
      change m∈(Finset.range k).image (fun i => axisSlope i s) at member
      obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp member
      exact Finset.mem_image.mpr ⟨offAxis i,Finset.mem_erase.mpr ⟨off_ne_on i s,
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)⟩,
        (axis_secant i s).trans ((congrArg some eq).trans value)⟩

theorem axis_degree_eq {k : ℕ} (hk : 8≤k) (odd : Bool) (s : ℤ) :
    (directions (configuration k odd) (onAxis s)).card=(axisValues k s).card+1 := by
  rw [axis_directions hk,Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ (Option.some_injective ℚ)]

def merged (k : ℕ) (odd : Bool) (i : ℕ) : Finset ℕ :=
  ((Finset.range k).erase i).filter (fun j => (i : ℤ)+j∈heights k odd)

theorem off_overlap (k : ℕ) (odd : Bool) (i : ℕ) :
    (((Finset.range k).erase i).image (secant i)) ∩ ((heights k odd).image (axisSlope i))=
      (merged k odd i).image (secant i) := by
  ext m
  constructor
  · intro h
    obtain ⟨ha,hb⟩ := Finset.mem_inter.mp h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨s,hs,eq⟩ := Finset.mem_image.mp hb
    have es := (shared_intercept i j s).mp eq.symm
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hj,es ▸ hs⟩)
  · intro h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hk,hs⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ hk,Finset.mem_image.mpr
      ⟨(i : ℤ)+j,hs,((shared_intercept ..).mpr rfl).symm⟩⟩

theorem off_degree_sum {k i : ℕ} (hk : 8≤k) (hi : i<k) (odd : Bool) :
    (directions (configuration k odd) (offAxis i)).card + (merged k odd i).card =
      (k-1)+(k+odd.toNat) := by
  rw [off_directions,Finset.card_image_of_injective _ (Option.some_injective ℚ)]
  have h := Finset.card_union_add_card_inter (((Finset.range k).erase i).image (secant i))
    ((heights k odd).image (axisSlope i))
  rw [off_overlap,Finset.card_image_of_injective _ (off_secant_injective i),
    Finset.card_image_of_injective _ (off_secant_injective i),
    Finset.card_image_of_injective _ (at_off_axis_injective i),
    Finset.card_erase_of_mem (Finset.mem_range.mpr hi),Finset.card_range,heights_card hk] at h
  exact h

end GyarfasPlanar
