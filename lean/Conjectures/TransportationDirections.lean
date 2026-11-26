import Conjectures.TransportationPolytope
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! The direction space of the affine hull is determined by the entries in
the first two rows of the small columns. -/

namespace TransportationEhrhart

abbrev Coordinates (m : ℕ) := Fin 2 × Fin m → ℝ

def coordinates (m : ℕ) : RealTable m →ₗ[ℝ] Coordinates m where
  toFun p e := p e.1.castSucc (some e.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def homogeneous (m : ℕ) : Submodule ℝ (RealTable m) where
  carrier := {a | (∀ i,∑ j,a i j=0) ∧ ∀ j,∑ i,a i j=0}
  add_mem' := by
    rintro x y ⟨xr,xc⟩ ⟨yr,yc⟩
    constructor <;> intro t
    · change (∑ j,(x t j+y t j))=0
      rw [Finset.sum_add_distrib,xr,yr,add_zero]
    · change (∑ i,(x i t+y i t))=0
      rw [Finset.sum_add_distrib,xc,yc,add_zero]
  zero_mem' := by constructor <;> simp
  smul_mem' := by
    rintro c x ⟨xr,xc⟩
    constructor <;> intro t
    · change (∑ j,c*x t j)=0
      rw [←Finset.mul_sum,xr,mul_zero]
    · change (∑ i,c*x i t)=0
      rw [←Finset.mul_sum,xc,mul_zero]

theorem directions_homogeneous (m : ℕ) : vectorSpan ℝ (polytope m) ≤ homogeneous m := by
  rw [vectorSpan_def]
  apply Submodule.span_le.mpr
  rintro x ⟨a,ha,b,hb,rfl⟩
  obtain ⟨_,ra,ca⟩ := ha
  obtain ⟨_,rb,cb⟩ := hb
  constructor <;> intro j
  · change ∑ t,(a j t-b j t)=0
    rw [Finset.sum_sub_distrib,ra,rb,sub_self]
  · change ∑ t,(a t j-b t j)=0
    rw [Finset.sum_sub_distrib,ca,cb,sub_self]

theorem homogeneous_coordinates_zero {m : ℕ} {x : RealTable m} (h : x∈homogeneous m)
    (hz : coordinates m x=0) : x=0 := by
  obtain ⟨row,col⟩ := h
  have small (i : Fin 2) (j : Fin m) : x i.castSucc (some j)=0 := congrFun hz (i,j)
  have top (i : Fin 2) (j : Col m) : x i.castSucc j=0 := by
    cases j with
    | none =>
      have sum := row i.castSucc
      simpa [Fintype.sum_option,small i] using sum
    | some j => exact small i j
  funext i j
  fin_cases i
  · exact top 0 j
  · exact top 1 j
  · have sum := col j
    have h0 : x 0 j=0 := top 0 j
    have h1 : x 1 j=0 := top 1 j
    simpa [Fin.sum_univ_three,h0,h1] using sum

def directionCoordinates (m : ℕ) :
    vectorSpan ℝ (polytope m) →ₗ[ℝ] Coordinates m := (coordinates m).domRestrict _

theorem direction_injective (m : ℕ) : Function.Injective (directionCoordinates m) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  exact Subtype.ext (homogeneous_coordinates_zero (directions_homogeneous m x.property) hx)

end TransportationEhrhart
