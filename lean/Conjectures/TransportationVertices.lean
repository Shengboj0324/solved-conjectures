import Conjectures.TransportationDirections
import Conjectures.TransportationLattice

/-! One integral base table and 2m neighboring integral tables independently
vary all projected entries. Thus the real affine dimension is exactly 2m. -/

namespace TransportationEhrhart

def oneAt {m : ℕ} (c : Col m) : Row (Col m) 1 :=
  ⟨fun j => if j=c then 1 else 0,by simp⟩

def basePair (m : ℕ) : RowPair m 1 := (oneAt none,oneAt none)

def movedPair {m : ℕ} (e : Fin 2 × Fin m) : RowPair m 1 :=
  (oneAt (if e.1=0 then some e.2 else none),oneAt (if e.1=1 then some e.2 else none))

theorem base_admissible (m : ℕ) : Admissible (basePair m) := by
  intro j
  simp [basePair,oneAt]

theorem moved_admissible {m : ℕ} (e : Fin 2 × Fin m) : Admissible (movedPair e) := by
  rintro j
  rcases e with ⟨r,c⟩
  fin_cases r <;> by_cases h : j=c <;> simp [movedPair,oneAt,h]

def baseVertex (m : ℕ) := tableReal (makeTable (basePair m) (base_admissible m))
def movedVertex {m : ℕ} (e : Fin 2 × Fin m) := tableReal (makeTable (movedPair e) (moved_admissible e))

theorem base_mem (m : ℕ) : baseVertex m∈polytope m := tableReal_fits _
theorem moved_mem {m : ℕ} (e : Fin 2 × Fin m) : movedVertex e∈polytope m := tableReal_fits _

def elementaryDirection {m : ℕ} (e : Fin 2 × Fin m) : vectorSpan ℝ (polytope m) :=
  ⟨movedVertex e-baseVertex m,vsub_mem_vectorSpan ℝ (moved_mem e) (base_mem m)⟩

theorem elementary_coordinate {m : ℕ} (e t : Fin 2 × Fin m) :
    directionCoordinates m (elementaryDirection e) t=if e=t then 1 else 0 := by
  rcases e with ⟨r,c⟩
  rcases t with ⟨s,j⟩
  fin_cases r <;> fin_cases s <;> by_cases h : c=j <;>
    simp [directionCoordinates,coordinates,elementaryDirection,movedVertex,baseVertex,tableReal,
      makeTable,movedPair,basePair,oneAt,h,ne_comm]

theorem direction_surjective (m : ℕ) : Function.Surjective (directionCoordinates m) := by
  classical
  intro y
  refine ⟨∑ e,y e • elementaryDirection e,?_⟩
  funext t
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,elementary_coordinate]
  simp [mul_ite]

theorem affine_dimension (m : ℕ) : Module.finrank ℝ (vectorSpan ℝ (polytope m))=2*m := by
  have iso := LinearEquiv.ofBijective (directionCoordinates m) ⟨direction_injective m,direction_surjective m⟩
  calc
    _ = Module.finrank ℝ (Coordinates m) := iso.finrank_eq
    _ = 2*m := by simp [Coordinates,Fintype.card_prod]

end TransportationEhrhart
