import Conjectures.GyarfasPlanarLabels

/-! A degree has at most two labels. Inside the off-axis list, labels two
places apart have different degrees. The only cross-family tie is at the
first label of either family and occurs at even order. -/

namespace GyarfasPlanar

theorem off_two_apart {k i j : ℕ} (hk : 8≤k) (odd : Bool) (apart : i+2≤j) (hj : j<k) :
    offDegree k odd i<offDegree k odd j := by
  unfold offDegree
  split_ifs <;> omega

theorem mixed_equality {k i j : ℕ} (hk : 8≤k) (odd : Bool) (hi : i<k)
    (hj : j<k+odd.toNat) (eq : offDegree k odd i=axisDegree k j) :
    i=0 ∧ j=0 ∧ odd=false := by
  unfold offDegree axisDegree at eq
  cases odd <;> simp only [Bool.toNat_false,Bool.toNat_true] at eq hj <;>
    split_ifs at eq <;> simp <;> omega

private theorem axis_three {k i j l : ℕ} (hk : 8≤k) (odd : Bool)
    (ij : i<j) (jl : j<l) (hl : l<k+odd.toNat)
    (h₁ : axisDegree k i=axisDegree k j) (h₂ : axisDegree k j=axisDegree k l) : False := by
  unfold axisDegree at h₁ h₂
  cases odd <;> simp only [Bool.toNat_false,Bool.toNat_true] at hl <;>
    split_ifs at h₁ h₂ <;> omega

theorem no_three_labels {k a b c : ℕ} (hk : 8≤k) (odd : Bool)
    (ab : a<b) (bc : b<c) (hc : c<2*k+odd.toNat)
    (h₁ : labelDegree k odd a=labelDegree k odd b)
    (h₂ : labelDegree k odd b=labelDegree k odd c) : False := by
  by_cases lowB : b<k
  · have lowA : a<k := by omega
    have h := h₁.trans h₂
    by_cases lowC : c<k
    · have lt := off_two_apart hk odd (i := a) (j := c) (by omega) lowC
      exact lt.ne (by simpa [labelDegree,lowA,lowC] using h)
    · have cBound : c-k<k+odd.toNat := by omega
      have x := mixed_equality hk odd lowA cBound (by simpa [labelDegree,lowA,lowC] using h)
      have y := mixed_equality hk odd lowB cBound (by simpa [labelDegree,lowB,lowC] using h₂)
      omega
  · have highC : ¬c<k := by omega
    have bBound : b-k<k+odd.toNat := by omega
    have cBound : c-k<k+odd.toNat := by omega
    by_cases lowA : a<k
    · have h := h₁.trans h₂
      have x := mixed_equality hk odd lowA bBound (by simpa [labelDegree,lowA,lowB] using h₁)
      have y := mixed_equality hk odd lowA cBound (by simpa [labelDegree,lowA,highC] using h)
      omega
    · exact axis_three hk odd (i := a-k) (j := b-k) (l := c-k) (by omega) (by omega) cBound
        (by simpa [labelDegree,lowA,lowB] using h₁) (by simpa [labelDegree,lowB,highC] using h₂)

private theorem any_three_labels {k a b c : ℕ} (hk : 8≤k) (odd : Bool)
    (ha : a<2*k+odd.toNat) (hb : b<2*k+odd.toNat) (hc : c<2*k+odd.toNat)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (eq₁ : labelDegree k odd a=labelDegree k odd b)
    (eq₂ : labelDegree k odd b=labelDegree k odd c) : False := by
  have h := eq₁.trans eq₂
  rcases lt_or_gt_of_ne hab with ab|ba <;> rcases lt_or_gt_of_ne hac with ac|ca <;>
    rcases lt_or_gt_of_ne hbc with bc|cb
  all_goals first
    | exact no_three_labels hk odd ab bc hc eq₁ eq₂
    | exact no_three_labels hk odd ac cb hb h eq₂.symm
    | exact no_three_labels hk odd ba ac hc eq₁.symm h
    | exact no_three_labels hk odd bc ca ha eq₂ h.symm
    | exact no_three_labels hk odd ca ab hb h.symm eq₁
    | exact no_three_labels hk odd cb ba ha eq₂.symm eq₁.symm

theorem uniform_multiplicity {k : ℕ} (hk : 8≤k) (odd : Bool) (d : ℕ) :
    rationalMultiplicity (configuration k odd) d≤2 := by
  by_contra! h
  obtain ⟨p,q,r,hp,hq,hr,pq,pr,qr⟩ := Finset.two_lt_card_iff.mp h
  have index {x} (hx : x∈(configuration k odd).filter (fun x => (directions (configuration k odd) x).card=d)) :
      ∃ i, i<2*k+odd.toNat ∧ labelPoint k i=x ∧ labelDegree k odd i=d := by
    obtain ⟨mem,eq⟩ := Finset.mem_filter.mp hx
    rw [configuration_labels hk] at mem
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp mem
    have bound := Finset.mem_range.mp hi
    exact ⟨i,bound,rfl,(label_degree hk odd bound).symm.trans eq⟩
  obtain ⟨i,hi,rfl,di⟩ := index hp
  obtain ⟨j,hj,rfl,dj⟩ := index hq
  obtain ⟨l,hl,rfl,dl⟩ := index hr
  exact any_three_labels hk odd hi hj hl (fun h => pq (congrArg _ h)) (fun h => pr (congrArg _ h))
    (fun h => qr (congrArg _ h)) (di.trans dj.symm) (dj.trans dl.symm)

end GyarfasPlanar
