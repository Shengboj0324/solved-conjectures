import Conjectures.GyarfasPlanarLines
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Rational slope computations count the distinct spanned lines in the
real affine plane after embedding the rational construction. -/

namespace GyarfasPlanar

def realPoint (p : Point ℚ) : Point ℝ := (p.1,p.2)

theorem realPoint_injective : Function.Injective realPoint := by
  intro p q eq
  apply Prod.ext
  · exact Rat.cast_injective (α := ℝ) (congrArg (fun z : Point ℝ => z.1) eq)
  · exact Rat.cast_injective (α := ℝ) (congrArg (fun z : Point ℝ => z.2) eq)

theorem direction_realPoint (p q : Point ℚ) :
    direction (realPoint p) (realPoint q)=(direction p q).map (fun a : ℚ => (a : ℝ)) := by
  by_cases h : q.1=p.1
  · simp [direction,realPoint,h]
  · simp [direction,realPoint,h]

theorem card_real_lines (P : Finset (Point ℚ)) (p : Point ℚ) :
    (spannedLines (P.image realPoint) (realPoint p)).card=(directions P p).card := by
  classical
  rw [card_spannedLines]
  have eq : directions (P.image realPoint) (realPoint p)=
      (directions P p).image (Option.map (fun a : ℚ => (a : ℝ))) := by
    unfold directions
    rw [←Finset.image_erase realPoint_injective,Finset.image_image,Finset.image_image]
    apply Finset.image_congr
    intro q _
    exact direction_realPoint p q
  rw [eq,Finset.card_image_of_injective]
  exact Option.map_injective (Rat.cast_injective (α := ℝ))

noncomputable def multiplicity (P : Finset (Point ℝ)) (d : ℕ) : ℕ := by
  classical
  exact (P.filter (fun p => (spannedLines P p).card=d)).card

def rationalMultiplicity (P : Finset (Point ℚ)) (d : ℕ) :=
  (P.filter (fun p => (directions P p).card=d)).card

theorem multiplicity_real (P : Finset (Point ℚ)) (d : ℕ) :
    multiplicity (P.image realPoint) d=rationalMultiplicity P d := by
  classical
  have eq : ((P.image realPoint).filter (fun p => (spannedLines (P.image realPoint) p).card=d))=
      (P.filter (fun p => (directions P p).card=d)).image realPoint := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,h⟩
      exact ⟨p,⟨hp,(card_real_lines P p) ▸ h⟩,rfl⟩
    · rintro ⟨p,⟨hp,h⟩,rfl⟩
      exact ⟨⟨p,hp,rfl⟩,(card_real_lines P p).trans h⟩
  unfold multiplicity rationalMultiplicity
  rw [eq,Finset.card_image_of_injective _ realPoint_injective]

theorem axis_triangle_noncollinear {P : Finset (Point ℚ)}
    (h₀ : (0,0)∈P) (h₂ : (0,2)∈P) (h₁ : (1,0)∈P) :
    ¬Collinear ℝ (↑(P.image realPoint) : Set (Point ℝ)) := by
  intro col
  have cast_mem (p : Point ℚ) (hp : p∈P) : realPoint p∈(↑(P.image realPoint) : Set (Point ℝ)) :=
    Finset.mem_image_of_mem _ hp
  have neq : realPoint (0,0)≠realPoint (0,2) := fun e =>
    (show ((0,0) : Point ℚ)≠(0,2) by decide) (realPoint_injective e)
  have line := col.mem_affineSpan_of_mem_of_ne (cast_mem _ h₀) (cast_mem _ h₂) (cast_mem _ h₁) neq
  change realPoint (1,0)∈(affineSpan ℝ ({realPoint (0,0),realPoint (0,2)} : Set (Point ℝ)) : Set (Point ℝ)) at line
  rw [spanned_line neq.symm] at line
  norm_num [direction,locus,realPoint] at line

end GyarfasPlanar
