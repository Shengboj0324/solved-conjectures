import Conjectures.NathansonSidonSystems
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-! The extremal size is attained. Counting actual output fibers in their
integer interval bounds every allowed multiplicity. -/

namespace NathansonSidon

variable {h : ℕ}

theorem zero_feasible (hh : 0<h) (c : Fin h → ℤ) (N g : ℕ) : Feasible c N g 0 := by
  classical
  let A : Fin h → Finset ℤ := fun _ => ∅
  refine ⟨A,by simp [A],fun z => ?_⟩
  have empty : Fintype.piFinset A=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact Finset.notMem_empty (x ⟨0,hh⟩) (Fintype.mem_piFinset.mp hx ⟨0,hh⟩)
  simp [representations,empty]

theorem extremal_feasible (hh : 0<h) (c : Fin h → ℤ) (N g : ℕ) :
    Feasible c N g (extremal c N g) := by
  classical
  let s := (Finset.range (N+1)).filter (Feasible c N g)
  have zero : 0 ∈ s := Finset.mem_filter.mpr ⟨by simp,zero_feasible hh c N g⟩
  obtain ⟨q,hq,eq⟩ := Finset.exists_mem_eq_sup s ⟨0,zero⟩ id
  change Feasible c N g (s.sup id)
  rw [eq]
  exact (Finset.mem_filter.mp hq).2

def coefficientSum (c : Fin h → ℤ) : ℕ := ∑ i,(c i).natAbs

private def lower (c : ℤ) (N : ℕ) : ℤ := if 0≤c then c else c*N

private theorem coordinate_bounds {c x : ℤ} {N : ℕ} (hx : x ∈ Finset.Icc 1 (N : ℤ)) :
    lower c N≤c*x ∧ c*x≤lower c N+(c.natAbs : ℤ)*((N : ℤ)-1) := by
  obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hx
  rw [Int.natCast_natAbs]
  by_cases pos : 0≤c
  · simp only [lower,pos,↓reduceIte,abs_of_nonneg pos]
    constructor
    · simpa using mul_le_mul_of_nonneg_left lo pos
    · have := mul_le_mul_of_nonneg_left hi pos
      linarith
  · have neg : c≤0 := by omega
    simp only [lower,pos,↓reduceIte,abs_of_nonpos neg]
    constructor
    · exact mul_le_mul_of_nonpos_left hi neg
    · have := mul_le_mul_of_nonpos_left lo neg
      linarith

theorem feasible_diameter {c : Fin h → ℤ} {N g q : ℕ} (hh : 0<h) (w : Feasible c N g q) :
    q^h≤g*(coefficientSum c*(N-1)+1) := by
  classical
  by_cases npos : 1≤N
  · obtain ⟨A,sets,mult⟩ := w
    let a := ∑ i,lower (c i) N
    let width := coefficientSum c*(N-1)
    let t := Finset.Icc a (a+(width : ℤ))
    have maps : ∀ x∈Fintype.piFinset A,output c x∈t := by
      intro x hx
      have bounds (i : Fin h) := coordinate_bounds ((sets i).1 (Fintype.mem_piFinset.mp hx i)) (c := c i)
      apply Finset.mem_Icc.mpr
      refine ⟨Finset.sum_le_sum (fun i _ => (bounds i).1),?_⟩
      have hi := Finset.sum_le_sum (s := Finset.univ) fun i _ => (bounds i).2
      rw [Finset.sum_add_distrib,←Finset.sum_mul] at hi
      dsimp [a,width,coefficientSum]
      push_cast [Nat.cast_sub npos]
      simpa only [output,Int.natCast_natAbs] using hi
    have count := Finset.card_le_mul_card_image_of_maps_to maps g fun z _ => mult z
    have cp : (Fintype.piFinset A).card=q^h := by simp [Fintype.card_piFinset,fun i => (sets i).2]
    have ct : t.card=width+1 := by
      rw [show t=Finset.Icc a (a+(width : ℤ)) from rfl,Int.card_Icc]
      omega
    rwa [cp,ct] at count
  · have size := feasible_le_size hh w
    have eq : q=0 := by omega
    simp [eq,Nat.ne_of_gt hh]

theorem extremal_diameter (hh : 0<h) (c : Fin h → ℤ) (N g : ℕ) :
    (extremal c N g)^h≤g*(coefficientSum c*(N-1)+1) :=
  feasible_diameter hh (extremal_feasible hh c N g)

end NathansonSidon
