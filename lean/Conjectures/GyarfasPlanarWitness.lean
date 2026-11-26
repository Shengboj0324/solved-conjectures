import Conjectures.GyarfasPlanarRational

/-! The first order of the published rational construction already answers the
original existence question about genuine spanned lines in the real plane. -/

namespace GyarfasPlanar

def offAxis (i : ℕ) : Point ℚ :=
  (1/((i : ℚ)+1),(i : ℚ)^2/((i : ℚ)+1))

def onAxis (s : ℤ) : Point ℚ := (0,s)

def heights (k : ℕ) (odd : Bool) : Finset ℤ :=
  let common := insert (2*(k : ℤ)-3) (((Finset.range k).image Int.ofNat).erase 1)
  if odd then insert (-1) common else common

def configuration (k : ℕ) (odd : Bool) : Finset (Point ℚ) :=
  ((Finset.range k).image offAxis) ∪ ((heights k odd).image onAxis)

theorem multiplicity_from_points (P : Finset (Point ℚ)) (d bound : ℕ)
    (h : ∀ p∈P, rationalMultiplicity P (directions P p).card≤bound) :
    rationalMultiplicity P d≤bound := by
  by_cases ex : ∃ p∈P, (directions P p).card=d
  · obtain ⟨p,hp,rfl⟩ := ex
    exact h p hp
  · have empty : (P.filter (fun p => (directions P p).card=d))=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro p hp eq
      exact ex ⟨p,hp,eq⟩
    simp [rationalMultiplicity,empty]

theorem sixteen_count : (configuration 8 false).card=16 := by decide +kernel

private theorem sixteen_origin : ((0,0) : Point ℚ)∈configuration 8 false := by decide +kernel
private theorem sixteen_axis : ((0,2) : Point ℚ)∈configuration 8 false := by decide +kernel
private theorem sixteen_off : ((1,0) : Point ℚ)∈configuration 8 false := by decide +kernel

theorem sixteen_rational_multiplicity (d : ℕ) : rationalMultiplicity (configuration 8 false) d≤2 := by
  apply multiplicity_from_points
  decide +kernel

theorem sixteen_attains_two : rationalMultiplicity (configuration 8 false) 9=2 := by decide +kernel

theorem sixteen_real :
    let S := (configuration 8 false).image realPoint
    S.card=16 ∧ ¬Collinear ℝ (↑S : Set (Point ℝ)) ∧
      (∀ d, multiplicity S d≤2) ∧ multiplicity S 9=2 := by
  refine ⟨(Finset.card_image_of_injective _ realPoint_injective).trans sixteen_count,
    axis_triangle_noncollinear sixteen_origin sixteen_axis sixteen_off,?_,?_⟩
  · intro d
    exact (multiplicity_real _ d) ▸ sixteen_rational_multiplicity d
  · exact (multiplicity_real _ 9).trans sixteen_attains_two

end GyarfasPlanar
