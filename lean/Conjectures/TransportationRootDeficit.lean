import Conjectures.TransportationRolleWindow

/-! If subtracting a linear term clears an interval containing many roots,
the perturbed polynomial loses almost as many real roots. Localized Rolle
counts on the two exterior rays handle all multiplicities and both tails. -/

namespace TransportationEhrhart

open Polynomial Set

theorem interval_partition (p : ℝ[X]) {a b : ℝ} (ab : a≤b) :
    (rootsIn p (Iio a)).card+(rootsIn p (Icc a b)).card+(rootsIn p (Ioi b)).card=p.roots.card := by
  classical
  have eq : rootsIn p (Iio a)+rootsIn p (Icc a b)+rootsIn p (Ioi b)=p.roots := by
    ext x
    simp only [rootsIn,Multiset.count_add,Multiset.count_filter,Set.mem_Iio,Set.mem_Icc,Set.mem_Ioi]
    rcases lt_or_ge x a with hx | hx
    · simp [hx,not_le_of_gt hx,not_lt_of_ge (hx.le.trans ab)]
    · rcases le_or_gt x b with hy | hy
      · simp [hx,hy,not_lt_of_ge hx,not_lt_of_ge hy]
      · simp [hx,hy,not_lt_of_ge hx,not_le_of_gt hy]
  simpa only [Multiset.card_add] using congrArg Multiset.card eq

theorem deficit_from_interval {p f : ℝ[X]} {a b : ℝ} (ab : a≤b)
    (same : p.derivative.derivative=f.derivative.derivative)
    (clear : ∀ x∈Icc a b,p.eval x≠0) (degree : 2≤p.natDegree) :
    p.roots.card+(rootsIn f (Icc a b)).card≤p.natDegree+4 := by
  classical
  have middle : rootsIn p (Icc a b)=0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    obtain ⟨root,inside⟩ := mem_rootsIn.mp hx
    exact clear x inside (isRoot_of_mem_roots root)
  have l := rolle_window_twice p (Iio a) inferInstance
  have r := rolle_window_twice p (Ioi b) inferInstance
  have ineq := rolle_window_twice f (Icc a b) inferInstance
  rw [←same] at ineq
  have outer := interval_partition p ab
  rw [middle,Multiset.card_zero,add_zero] at outer
  have total := interval_partition p.derivative.derivative ab
  have bound := p.derivative.derivative.card_roots'
  have d := natDegree_derivative_le p
  have dd := natDegree_derivative_le p.derivative
  omega

theorem deficit_linear {p f : ℝ[X]} {c : ℝ} {a b : ℝ} (ab : a≤b) (eq : p=f-C c*X)
    (clear : ∀ x∈Icc a b,p.eval x≠0) (degree : 2≤p.natDegree) :
    p.roots.card+(rootsIn f (Icc a b)).card≤p.natDegree+4 := by
  apply deficit_from_interval ab _ clear degree
  simp [eq]

end TransportationEhrhart
