import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Tactic

/-! A localized version of polynomial Rolle counting. Multiplicities at old
roots and the intervening derivative roots are counted separately. -/

namespace TransportationEhrhart

open Polynomial

noncomputable def rootsIn (p : ℝ[X]) (s : Set ℝ) : Multiset ℝ := by
  classical exact p.roots.filter (·∈s)

theorem mem_rootsIn {p : ℝ[X]} {s : Set ℝ} {x : ℝ} : x∈rootsIn p s ↔ x∈p.roots ∧ x∈s := by
  classical exact Multiset.mem_filter

theorem count_rootsIn (p : ℝ[X]) (s : Set ℝ) (x : ℝ) (hx : x∈s) :
    (rootsIn p s).count x=p.rootMultiplicity x := by
  classical simp [rootsIn,hx,count_roots]

theorem counted_intervals {u v : Multiset ℝ}
    (old : ∀ x∈u,u.count x-1≤v.count x)
    (gaps : u.toFinset.card≤(v.toFinset \ u.toFinset).card+1) : u.card≤v.card+1 := by
  classical
  have addOne : u.card=(∑ x ∈ u.toFinset,(u.count x-1))+u.toFinset.card := by
    rw [←Multiset.toFinset_sum_count_eq u,Finset.card_eq_sum_ones,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have pos := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hx)
    omega
  have each : (v.toFinset \ u.toFinset).card≤∑ x ∈ v.toFinset \ u.toFinset,v.count x := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro x hx
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp hx).1)
  have counted : (∑ x ∈ u.toFinset,v.count x)+(∑ x ∈ v.toFinset \ u.toFinset,v.count x)=v.card := by
    rw [←Finset.sum_union Finset.disjoint_sdiff,Multiset.sum_count_eq_card]
    intro x hx
    by_cases hu : x∈u.toFinset
    · exact Finset.mem_union_left _ hu
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Multiset.mem_toFinset.mpr hx,hu⟩)
  have older := Finset.sum_le_sum (s := u.toFinset) (f := fun x => u.count x-1) (g := fun x => v.count x)
    (fun x hx => old x (Multiset.mem_toFinset.mp hx))
  omega

theorem rolle_window (p : ℝ[X]) (s : Set ℝ) (connected : s.OrdConnected) :
    (rootsIn p s).card≤(rootsIn p.derivative s).card+1 := by
  classical
  by_cases zero : p.derivative=0
  · rw [eq_C_of_derivative_eq_zero zero]
    simp [rootsIn]
  have nz : p≠0 := by
    rintro rfl
    exact zero derivative_zero
  apply counted_intervals
  · intro x hx
    have ins := (mem_rootsIn.mp hx).2
    rw [count_rootsIn p s x ins,count_rootsIn p.derivative s x ins]
    exact rootMultiplicity_sub_one_le_derivative_rootMultiplicity _ _
  · apply Finset.card_le_sdiff_of_interleaved
    intro x hx y hy less _
    obtain ⟨rx,sx⟩ := mem_rootsIn.mp (Multiset.mem_toFinset.mp hx)
    obtain ⟨ry,sy⟩ := mem_rootsIn.mp (Multiset.mem_toFinset.mp hy)
    have eq : p.eval x=p.eval y := ((mem_roots nz).mp rx).trans ((mem_roots nz).mp ry).symm
    obtain ⟨z,hz,der⟩ := exists_deriv_eq_zero less p.continuousOn eq
    refine ⟨z,Multiset.mem_toFinset.mpr (mem_rootsIn.mpr ⟨?_,connected.out' sx sy ⟨hz.1.le,hz.2.le⟩⟩),hz⟩
    rw [mem_roots zero,IsRoot,←p.deriv]
    exact der

theorem rolle_window_twice (p : ℝ[X]) (s : Set ℝ) (connected : s.OrdConnected) :
    (rootsIn p s).card≤(rootsIn p.derivative.derivative s).card+2 := by
  have a := rolle_window p s connected
  have b := rolle_window p.derivative s connected
  omega

end TransportationEhrhart
