import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! A vertical direction or an ordinary slope parametrizes the genuine
affine lines spanned by a finite planar point set through one of its points. -/

namespace GyarfasPlanar

abbrev Point (K : Type*) := K × K

section Field
variable {K : Type*} [Field K] [DecidableEq K]

def direction (p q : Point K) : Option K :=
  if q.1=p.1 then none else some ((q.2-p.2)/(q.1-p.1))

def locus (p : Point K) : Option K → Set (Point K)
  | none => {z | z.1=p.1}
  | some m => {z | z.2-p.2=m*(z.1-p.1)}

omit [DecidableEq K] in
theorem locus_injective (p : Point K) : Function.Injective (locus p) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have e := (Set.ext_iff.mp h (p.1,p.2+1)).mp (show (p.1,p.2+1)∈locus p none from rfl)
      simp [locus] at e
  | some a =>
    cases b with
    | none =>
      have e := (Set.ext_iff.mp h (p.1,p.2+1)).mpr (show (p.1,p.2+1)∈locus p none from rfl)
      simp [locus] at e
    | some b =>
      have e := (Set.ext_iff.mp h (p.1+1,p.2+a)).mp (by simp [locus])
      simpa [locus] using congrArg some (show a=b by simpa [locus] using e)

theorem spanned_line {p q : Point K} (hne : q≠p) :
    (affineSpan K ({p,q} : Set (Point K)) : Set (Point K))=locus p (direction p q) := by
  ext z
  change z∈affineSpan K ({p,q} : Set (Point K)) ↔ _
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  have coords (t : K) : AffineMap.lineMap p q t =
      (t*(q.1-p.1)+p.1,t*(q.2-p.2)+p.2) := by
    rw [AffineMap.lineMap_apply_module']
    rfl
  simp only [coords]
  by_cases hx : q.1=p.1
  · rw [direction,ite_eq_left hx]
    change (∃ t : K, _=z) ↔ z.1=p.1
    have hy : q.2-p.2≠0 := sub_ne_zero.mpr (fun e => hne (Prod.ext hx e))
    constructor
    · rintro ⟨t,e⟩
      simpa [hx] using (congrArg Prod.fst e).symm
    · intro h
      refine ⟨(z.2-p.2)/(q.2-p.2),Prod.ext ?_ ?_⟩
      · simpa [hx] using h.symm
      · change (z.2-p.2)/(q.2-p.2)*(q.2-p.2)+p.2=z.2
        rw [div_mul_cancel₀ _ hy,sub_add_cancel]
  · rw [direction,ite_eq_right hx]
    change (∃ t : K, _=z) ↔ z.2-p.2=(q.2-p.2)/(q.1-p.1)*(z.1-p.1)
    have dx : q.1-p.1≠0 := sub_ne_zero.mpr hx
    constructor
    · rintro ⟨t,rfl⟩
      dsimp
      field_simp
      ring
    · intro h
      refine ⟨(z.1-p.1)/(q.1-p.1),Prod.ext ?_ ?_⟩
      · change (z.1-p.1)/(q.1-p.1)*(q.1-p.1)+p.1=z.1
        rw [div_mul_cancel₀ _ dx,sub_add_cancel]
      · change (z.1-p.1)/(q.1-p.1)*(q.2-p.2)+p.2=z.2
        calc
          _ = (q.2-p.2)/(q.1-p.1)*(z.1-p.1)+p.2 := by ring
          _ = _ := by rw [←h,sub_add_cancel]

def directions (P : Finset (Point K)) (p : Point K) : Finset (Option K) :=
  (P.erase p).image (direction p)

noncomputable def spannedLines (P : Finset (Point K)) (p : Point K) : Finset (Set (Point K)) := by
  classical
  exact (P.erase p).image fun q => (affineSpan K ({p,q} : Set (Point K)) : Set (Point K))

theorem card_spannedLines (P : Finset (Point K)) (p : Point K) :
    (spannedLines P p).card=(directions P p).card := by
  classical
  have eq : spannedLines P p=(directions P p).image (locus p) := by
    unfold spannedLines directions
    rw [Finset.image_image]
    apply Finset.image_congr
    intro q hq
    exact spanned_line (Finset.mem_erase.mp hq).1
  rw [eq,Finset.card_image_of_injective _ (locus_injective p)]

end Field
end GyarfasPlanar
