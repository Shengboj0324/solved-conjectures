import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-! Nathanson's extremal function for separate coordinate sets. The
multiplicity is the actual number of tuples giving a specified integer. -/

namespace NathansonSidon

variable {h : ℕ}

def output (c x : Fin h → ℤ) : ℤ := ∑ i,c i*x i

def representations (c : Fin h → ℤ) (A : Fin h → Finset ℤ) (z : ℤ) : ℕ :=
  ((Fintype.piFinset A).filter fun x => output c x=z).card

def Feasible (c : Fin h → ℤ) (N g q : ℕ) : Prop :=
  ∃ A : Fin h → Finset ℤ, (∀ i,A i⊆Finset.Icc 1 (N : ℤ) ∧ (A i).card=q) ∧
    ∀ z, representations c A z≤g

noncomputable def extremal (c : Fin h → ℤ) (N g : ℕ) : ℕ := by
  classical
  exact ((Finset.range (N+1)).filter (Feasible c N g)).sup id

theorem feasible_le_size {c : Fin h → ℤ} {N g q : ℕ} (hh : 0<h) (w : Feasible c N g q) : q≤N := by
  obtain ⟨A,ha,_⟩ := w
  obtain ⟨inc,eq⟩ := ha ⟨0,hh⟩
  have bound := Finset.card_le_card inc
  rw [eq,Int.card_Icc] at bound
  omega

theorem feasible_le_extremal {c : Fin h → ℤ} {N g q : ℕ} (hh : 0<h) (w : Feasible c N g q) :
    q≤extremal c N g := by
  classical
  have le := feasible_le_size hh w
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),w⟩)

theorem representations_le_one_of_injective (c : Fin h → ℤ) (A : Fin h → Finset ℤ)
    (inj : Set.InjOn (output c) (Fintype.piFinset A : Set (Fin h → ℤ))) (z : ℤ) :
    representations c A z≤1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨xA,ex⟩ := Finset.mem_filter.mp hx
  obtain ⟨yA,ey⟩ := Finset.mem_filter.mp hy
  exact inj xA yA (ex.trans ey.symm)

theorem feasible_mono_multiplicity {c : Fin h → ℤ} {N g g' q : ℕ} (le : g≤g') (w : Feasible c N g q) :
    Feasible c N g' q := by
  obtain ⟨A,ha,mult⟩ := w
  exact ⟨A,ha,fun z => (mult z).trans le⟩

end NathansonSidon
