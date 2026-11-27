import Conjectures.GyarfasPlanarOptimal

/-! The degrees attained by the configuration form a single integer interval.
Its cardinality differs from three quarters of the order by a bounded constant. -/

namespace GyarfasPlanar

noncomputable def spectrum (P : Finset (Point ℝ)) : Finset ℕ :=
  P.image fun p => (spannedLines P p).card

theorem spectrum_labels {k : ℕ} (hk : 8 ≤ k) (odd : Bool) :
    spectrum ((configuration k odd).image realPoint) =
      (Finset.range (2*k+odd.toNat)).image (labelDegree k odd) := by
  ext d
  constructor
  · intro hd
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [configuration_labels hk odd] at hp
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨t,ht,((card_real_lines _ _).trans
      (label_degree hk odd (Finset.mem_range.mp ht))).symm⟩
  · rintro hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    have member : labelPoint k t ∈ configuration k odd := by
      rw [configuration_labels hk odd]
      exact Finset.mem_image_of_mem _ ht
    exact Finset.mem_image.mpr ⟨_,Finset.mem_image_of_mem realPoint member,
      (card_real_lines _ _).trans (label_degree hk odd (Finset.mem_range.mp ht))⟩

private theorem discrete_intermediate (f : ℕ → ℕ) (t d : ℕ)
    (step : ∀ i < t, f (i+1) ≤ f i+1) (lo : f 0 ≤ d) (hi : d ≤ f t) :
    ∃ i ≤ t, f i=d := by
  induction t with
  | zero => exact ⟨0,by omega,by omega⟩
  | succ t ih =>
    by_cases h : d ≤ f t
    · obtain ⟨i,hit,eq⟩ := ih (fun i hi => step i (by omega)) h
      exact ⟨i,by omega,eq⟩
    · have inc := step t (by omega)
      exact ⟨t+1,by omega,by omega⟩

private theorem off_bounds {k i : ℕ} (hk : 8 ≤ k) (hi : i<k) (odd : Bool) :
    k+odd.toNat+1 ≤ offDegree k odd i ∧ offDegree k odd i ≤ 2*k+odd.toNat-3 := by
  unfold offDegree
  split_ifs <;> omega

private theorem off_attains {k d : ℕ} (hk : 8 ≤ k) (odd : Bool)
    (lo : k+odd.toNat+1 ≤ d) (hi : d ≤ 2*k+odd.toNat-3) :
    ∃ i<k, offDegree k odd i=d := by
  have step (i : ℕ) (_ : i<k-1) : offDegree k odd (i+1) ≤ offDegree k odd i+1 := by
    unfold offDegree
    split_ifs <;> omega
  have first : offDegree k odd 0 ≤ d := by unfold offDegree; split_ifs <;> omega
  have last : d ≤ offDegree k odd (k-1) := by unfold offDegree; split_ifs <;> omega
  obtain ⟨i,hit,eq⟩ := discrete_intermediate _ (k-1) d step first last
  exact ⟨i,by omega,eq⟩

private theorem axis_attains {k d : ℕ} (hk : 8 ≤ k)
    (lo : k+1-k/2 ≤ d) (hi : d ≤ k+1) : ∃ i<k, axisDegree k i=d := by
  by_cases top : d=k+1
  · exact ⟨0,by omega,by simp [axisDegree,show (0:ℕ)≠k by omega,top]⟩
  · let i := 2*(k+1-d)-1
    have hit : i<k := by dsimp [i]; omega
    refine ⟨i,hit,?_⟩
    rw [axisDegree,ite_eq_right (by omega)]
    dsimp [i]; omega

theorem spectrum_interval {k : ℕ} (hk : 8 ≤ k) (odd : Bool) :
    spectrum ((configuration k odd).image realPoint) = Finset.Icc (k+1-k/2) (2*k+odd.toNat-3) := by
  rw [spectrum_labels hk odd]
  have e : odd.toNat ≤ 1 := by cases odd <;> decide
  ext d
  constructor
  · intro hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    have h := Finset.mem_range.mp ht
    apply Finset.mem_Icc.mpr
    by_cases low : t<k
    · rw [labelDegree,ite_eq_left low]
      obtain ⟨a,b⟩ := off_bounds hk low odd
      exact ⟨by omega,b⟩
    · rw [labelDegree,ite_eq_right low,axisDegree]
      split_ifs <;> omega
  · intro hd
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hd
    by_cases h : d ≤ k+1
    · obtain ⟨i,hit,eq⟩ := axis_attains hk lo h
      exact Finset.mem_image.mpr ⟨k+i,Finset.mem_range.mpr (by omega),
        by simpa [labelDegree,show ¬k+i<k by omega] using eq⟩
    · obtain ⟨i,hit,eq⟩ := off_attains hk odd (by omega) hi
      exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),by simpa [labelDegree,hit] using eq⟩

theorem spectrum_card {k : ℕ} (hk : 8 ≤ k) (odd : Bool) :
    (spectrum ((configuration k odd).image realPoint)).card = k+k/2-3+odd.toNat := by
  rw [spectrum_interval hk odd,Nat.card_Icc]
  omega

theorem spectrum_error {k : ℕ} (hk : 8 ≤ k) (odd : Bool) :
    let s := (spectrum ((configuration k odd).image realPoint)).card
    4*s+11 ≤ 3*(2*k+odd.toNat) ∧ 3*(2*k+odd.toNat) ≤ 4*s+14 := by
  dsimp only
  rw [spectrum_card hk odd]
  have e : odd.toNat ≤ 1 := by cases odd <;> decide
  omega

end GyarfasPlanar
