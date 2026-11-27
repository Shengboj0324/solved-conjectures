import Conjectures.ErdosGyarfasSpectrumIncidence
import Conjectures.GyarfasPlanarLines
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Intersecting the actual affinely spanned real lines with a finite
noncollinear point set produces a nontrivial finite linear space. -/

namespace ErdosGyarfasSpectrum

abbrev PlanePoint := GyarfasPlanar.Point ℝ

def lineSet (p q : PlanePoint) : Set PlanePoint := (line[ℝ,p,q] : Set PlanePoint)

noncomputable def traceLine (P : Finset PlanePoint) (L : Set PlanePoint) : Finset PlanePoint := by
  classical
  exact P.filter (·∈L)

noncomputable def planarLines (P : Finset PlanePoint) : Finset (Finset PlanePoint) := by
  classical
  exact P.biUnion (fun p => (P.erase p).image fun q => traceLine P (lineSet p q))

theorem mem_trace (P : Finset PlanePoint) (L : Set PlanePoint) (p : PlanePoint) :
    p∈traceLine P L ↔ p∈P ∧ p∈L := by
  classical
  simp [traceLine]

theorem mem_planarLines (P : Finset PlanePoint) (l : Finset PlanePoint) :
    l∈planarLines P ↔ ∃ a∈P, ∃ b∈P, b≠a ∧ traceLine P (lineSet a b)=l := by
  classical
  simp only [planarLines,Finset.mem_biUnion,Finset.mem_image,Finset.mem_erase]
  constructor
  · rintro ⟨a,ha,b,⟨ne,hb⟩,eq⟩; exact ⟨a,ha,b,hb,ne,eq⟩
  · rintro ⟨a,ha,b,hb,ne,eq⟩; exact ⟨a,ha,b,⟨ne,hb⟩,eq⟩

theorem common_line {a b p q : PlanePoint} (hab : a≠b) (hpq : p≠q)
    (hp : p∈lineSet a b) (hq : q∈lineSet a b) : lineSet p q=lineSet a b := by
  have c : Collinear ℝ ({p,q,a,b} : Set PlanePoint) := collinear_insert_insert_of_mem_affineSpan_pair hp hq
  have e := (c.affineSpan_eq_of_ne (show p∈({p,q,a,b} : Set PlanePoint) by simp)
    (show q∈({p,q,a,b} : Set PlanePoint) by simp) hpq).trans
    (c.affineSpan_eq_of_ne (show a∈({p,q,a,b} : Set PlanePoint) by simp)
    (show b∈({p,q,a,b} : Set PlanePoint) by simp) hab).symm
  exact congrArg SetLike.coe e

theorem collinear_lineSet (p q : PlanePoint) : Collinear ℝ (lineSet p q) := by
  have c := collinear_pair ℝ p q
  unfold Collinear lineSet
  rw [←direction_affineSpan,AffineSubspace.affineSpan_coe,direction_affineSpan]
  exact c

private theorem noncollinear_order (P : Finset PlanePoint) (h : ¬Collinear ℝ (P : Set PlanePoint)) :
    3≤P.card := by
  classical
  by_contra! small
  have sizes : P.card=0 ∨ P.card=1 ∨ P.card=2 := by omega
  apply h
  rcases sizes with z|o|t
  · obtain rfl := Finset.card_eq_zero.mp z
    simpa using collinear_empty ℝ (P := PlanePoint)
  · obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp o
    simpa using collinear_singleton ℝ p
  · obtain ⟨p,q,_,rfl⟩ := Finset.card_eq_two.mp t
    simpa using collinear_pair ℝ p q

theorem plane_space (P : Finset PlanePoint) (nc : ¬Collinear ℝ (P : Set PlanePoint)) :
    LinearOn P (planarLines P) := by
  classical
  refine ⟨noncollinear_order P nc,?_,?_,?_⟩
  · intro l hl
    obtain ⟨a,_,b,_,_,rfl⟩ := (mem_planarLines P l).mp hl
    exact fun p hp => ((mem_trace _ _ p).mp hp).1
  · intro l hl
    obtain ⟨a,ha,b,hb,ne,rfl⟩ := (mem_planarLines P l).mp hl
    have m₁ := (mem_trace P (lineSet a b) a).mpr ⟨ha,left_mem_affineSpan_pair ℝ a b⟩
    have m₂ := (mem_trace P (lineSet a b) b).mpr ⟨hb,right_mem_affineSpan_pair ℝ a b⟩
    refine ⟨Finset.Nontrivial.two_le_card ⟨a,m₁,b,m₂,ne.symm⟩,?_⟩
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun p hp => ((mem_trace _ _ p).mp hp).1,?_⟩
    intro eq
    apply nc
    apply (collinear_lineSet a b).subset
    intro p hp
    have member : p∈traceLine P (lineSet a b) := by rw [eq]; exact hp
    exact ((mem_trace _ _ p).mp member).2
  · intro p hp q hq ne
    refine ⟨traceLine P (lineSet p q),⟨(mem_planarLines _ _).mpr ⟨p,hp,q,hq,ne.symm,rfl⟩,
      (mem_trace _ _ _).mpr ⟨hp,left_mem_affineSpan_pair ℝ _ _⟩,
      (mem_trace _ _ _).mpr ⟨hq,right_mem_affineSpan_pair ℝ _ _⟩⟩,?_⟩
    rintro l ⟨hl,pl,ql⟩
    obtain ⟨a,_,b,_,hne,rfl⟩ := (mem_planarLines P l).mp hl
    exact congrArg (traceLine P) (common_line hne.symm ne ((mem_trace _ _ _).mp pl).2
      ((mem_trace _ _ _).mp ql).2).symm

end ErdosGyarfasSpectrum
