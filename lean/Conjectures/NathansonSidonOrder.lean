import Conjectures.NathansonSidonSteps
import Mathlib.Data.Finset.Max

/-! Permuting the coordinates preserves every value's multiplicity. One may
therefore put a smallest absolute coefficient first and a largest one last. -/

namespace NathansonSidon

theorem output_reindex {h : ℕ} (e : Equiv.Perm (Fin h)) (c x : Fin h → ℤ) :
    output (c ∘ e) (x ∘ e)=output c x :=
  Equiv.sum_comp e (fun i => c i*x i)

theorem representations_reindex {h : ℕ} (e : Equiv.Perm (Fin h)) (c : Fin h → ℤ)
    (A : Fin h → Finset ℤ) (z : ℤ) : representations c A z=representations (c ∘ e) (A ∘ e) z := by
  classical
  unfold representations
  apply Finset.card_bij' (fun x _ => x ∘ e) (fun x _ => x ∘ e.symm)
  · intro x hx
    obtain ⟨mem,eq⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => Fintype.mem_piFinset.mp mem (e i)),
      (output_reindex e c x).trans eq⟩
  · intro y hy
    obtain ⟨mem,eq⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      simpa [Function.comp_def] using Fintype.mem_piFinset.mp mem (e.symm i)
    · have val := output_reindex e c (y ∘ e.symm)
      simpa [Function.comp_def] using val.symm.trans (show output (c ∘ e) ((y ∘ e.symm) ∘ e)=z by
        simpa [Function.comp_def] using eq)
  · intro x _; funext i; simp
  · intro x _; funext i; simp

theorem feasible_reindex {h N g q : ℕ} (e : Equiv.Perm (Fin h)) (c : Fin h → ℤ) :
    Feasible c N g q ↔ Feasible (c ∘ e) N g q := by
  constructor
  · rintro ⟨A,ha,mult⟩
    exact ⟨A ∘ e,fun i => ha (e i),fun z => (representations_reindex e c A z) ▸ mult z⟩
  · rintro ⟨A,ha,mult⟩
    refine ⟨A ∘ e.symm,fun i => ha (e.symm i),fun z => ?_⟩
    have v := representations_reindex e c (A ∘ e.symm) z
    have eq : (A ∘ e.symm) ∘ e=A := by funext i; simp
    rw [eq] at v
    exact v ▸ mult z

theorem arranged {h : ℕ} (hh : 2≤h) (b : Fin h → ℕ) :
    ∃ e : Equiv.Perm (Fin h),
      (∀ i,b (e (firstIndex (by omega)))≤b i) ∧ (∀ i,b i≤b (e (lastIndex (by omega)))) := by
  classical
  let o : Fin h := firstIndex (by omega)
  let z : Fin h := lastIndex (by omega)
  have oz : o≠z := by
    intro eq
    have v := congrArg Fin.val eq
    dsimp [o,z,firstIndex,lastIndex] at v; omega
  have nonempty : (Finset.univ : Finset (Fin h)).Nonempty := ⟨o,Finset.mem_univ _⟩
  obtain ⟨m,_,small⟩ := Finset.exists_min_image Finset.univ b nonempty
  obtain ⟨M,_,big⟩ := Finset.exists_max_image Finset.univ b nonempty
  by_cases same : b m=b M
  · refine ⟨Equiv.refl _,fun i => ?_,fun i => ?_⟩
    · exact (big _ (Finset.mem_univ _)).trans (same ▸ small i (Finset.mem_univ _))
    · exact (big _ (Finset.mem_univ _)).trans (same ▸ small _ (Finset.mem_univ _))
  · have ne : m≠M := fun e => same (congrArg b e)
    let swap := Equiv.swap o m
    let j := swap.symm M
    have so : swap o=m := Equiv.swap_apply_left _ _
    have oj : o≠j := by
      intro eq
      have v := congrArg swap eq
      simp [j,so,ne] at v
    let e := (Equiv.swap z j).trans swap
    have em : e o=m := by
      change swap (Equiv.swap z j o)=m
      rw [Equiv.swap_apply_of_ne_of_ne oz oj,so]
    have eM : e z=M := by
      change swap (Equiv.swap z j z)=M
      rw [Equiv.swap_apply_left,Equiv.apply_symm_apply]
    refine ⟨e,fun i => ?_,fun i => ?_⟩
    · change b (e o)≤b i
      rw [em]
      exact small _ (Finset.mem_univ _)
    · change b i≤b (e z)
      rw [eM]
      exact big _ (Finset.mem_univ _)

end NathansonSidon
