import Conjectures.GyarfasPlanarMultiplicity

/-! Every finite set of at least two real planar points repeats a degree:
the n points have degrees between 1 and n−1. The published construction
therefore attains the best possible maximum multiplicity. -/

namespace GyarfasPlanar

theorem positive_degree_lt {P : Finset (Point ℝ)} (hn : 2≤P.card) {p : Point ℝ} (hp : p∈P) :
    0<(spannedLines P p).card ∧ (spannedLines P p).card<P.card := by
  classical
  have size := Finset.card_erase_of_mem hp
  obtain ⟨q,hq⟩ := Finset.card_pos.mp (show 0<(P.erase p).card by omega)
  constructor
  · apply Finset.card_pos.mpr
    exact ⟨_,Finset.mem_image_of_mem (fun q => (affineSpan ℝ ({p,q} : Set (Point ℝ)) : Set (Point ℝ))) hq⟩
  · have lim : (spannedLines P p).card≤(P.erase p).card := Finset.card_image_le
    omega

theorem repeated_degree {P : Finset (Point ℝ)} (hn : 2≤P.card) : ∃ d, 2≤multiplicity P d := by
  classical
  let deg (p : Point ℝ) := (spannedLines P p).card
  by_contra! h
  have inj : Set.InjOn deg (↑P : Set (Point ℝ)) := by
    intro p hp q hq he
    by_contra ne
    have inc : ({p,q} : Finset (Point ℝ)) ⊆ P.filter (fun z => deg z=deg p) := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl|eq
      · exact Finset.mem_filter.mpr ⟨hp,rfl⟩
      · obtain rfl := Finset.mem_singleton.mp eq
        exact Finset.mem_filter.mpr ⟨hq,he.symm⟩
    have bound := Finset.card_le_card inc
    rw [Finset.card_pair ne] at bound
    exact (Nat.not_le_of_gt (h (deg p))) bound
  have inc : P.image deg⊆(Finset.range P.card).erase 0 := by
    intro d hd
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
    have b := positive_degree_lt hn hp
    exact Finset.mem_erase.mpr ⟨Nat.ne_of_gt b.1,Finset.mem_range.mpr b.2⟩
  have bound := Finset.card_le_card inc
  rw [Finset.card_image_of_injOn inj,Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)),
    Finset.card_range] at bound
  omega

theorem uniform_real {k : ℕ} (hk : 8≤k) (odd : Bool) :
    let P := (configuration k odd).image realPoint
    P.card=2*k+odd.toNat ∧ ¬Collinear ℝ (↑P : Set (Point ℝ)) ∧
      (∀ d, multiplicity P d≤2) ∧ ∃ d, multiplicity P d=2 := by
  let P := (configuration k odd).image realPoint
  have card : P.card=2*k+odd.toNat :=
    (Finset.card_image_of_injective _ realPoint_injective).trans (configuration_card hk odd)
  have upper (d : ℕ) : multiplicity P d≤2 := (multiplicity_real _ d) ▸ uniform_multiplicity hk odd d
  obtain ⟨d,lo⟩ := repeated_degree (P := P) (by omega)
  exact ⟨card,configuration_noncollinear hk odd,upper,d,Nat.le_antisymm (upper d) lo⟩

theorem every_order {n : ℕ} (hn : 16≤n) :
    ∃ S : Finset (Point ℚ), let P := S.image realPoint
      P.card=n ∧ ¬Collinear ℝ (↑P : Set (Point ℝ)) ∧
        (∀ d, multiplicity P d≤2) ∧ ∃ d, multiplicity P d=2 := by
  let k := n/2
  let odd := decide (n%2=1)
  have hk : 8≤k := by dsimp [k]; omega
  have size : 2*k+odd.toNat=n := by
    dsimp [k,odd]
    by_cases h : n%2=1 <;> simp [h] <;> omega
  obtain ⟨card,geom,upper,attains⟩ := uniform_real hk odd
  exact ⟨configuration k odd,card.trans size,geom,upper,attains⟩

end GyarfasPlanar
