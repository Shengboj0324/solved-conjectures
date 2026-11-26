import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! A maximum disjoint subfamily of a finite set system covers all candidates
by intersections with its selected members. -/

namespace SteinerSail

theorem finite_packing {α V : Type*} [DecidableEq α] [DecidableEq V]
    (A : Finset α) (support : α → Finset V) (D : ℕ)
    (size : ∀ a∈A,(support a).card=7)
    (cap : ∀ v : V,6*(A.filter fun a => v∈support a).card≤D) :
    ∃ M : Finset α,M⊆A ∧ (M : Set α).Pairwise (fun a b => Disjoint (support a) (support b)) ∧
      6*A.card≤7*D*M.card := by
  classical
  let family := A.powerset.filter fun (M : Finset α) => (M : Set α).Pairwise (fun a b => Disjoint (support a) (support b))
  have empty : ∅∈family := by simp [family]
  obtain ⟨M,hm,maximal⟩ := family.exists_max_image Finset.card ⟨∅,empty⟩
  obtain ⟨sub,pairwise⟩ := Finset.mem_filter.mp hm
  have subM := Finset.mem_powerset.mp sub
  let hits (a : α) := A.filter fun b => ¬Disjoint (support a) (support b)
  have cover : A⊆M.biUnion hits := by
    intro a ha
    apply Finset.mem_biUnion.mpr
    by_contra! miss
    have dis (b : α) (hb : b∈M) : Disjoint (support b) (support a) := by
      by_contra bad
      exact miss b hb (Finset.mem_filter.mpr ⟨ha,bad⟩)
    have outside : a∉M := by
      intro h
      have nil := disjoint_self.mp (dis a h)
      have count := size a ha
      simp [nil] at count
    have enlarged : insert a M∈family := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset ha subM),?_⟩
      intro x hx y hy ne
      rcases Finset.mem_insert.mp hx with xeq|xm
      · rcases Finset.mem_insert.mp hy with yeq|ym
        · exact (ne (xeq.trans yeq.symm)).elim
        · rw [xeq]; exact (dis y ym).symm
      · rcases Finset.mem_insert.mp hy with yeq|ym
        · rw [yeq]; exact dis x xm
        · exact pairwise xm ym ne
    have bound := maximal _ enlarged
    rw [Finset.card_insert_of_notMem outside] at bound
    omega
  have localBound (a : α) (ha : a∈M) : 6*(hits a).card≤7*D := by
    have covers : hits a⊆(support a).biUnion (fun v => A.filter fun b => v∈support b) := by
      intro b hb
      obtain ⟨ba,bad⟩ := Finset.mem_filter.mp hb
      obtain ⟨v,va,vb⟩ := Finset.not_disjoint_iff.mp bad
      exact Finset.mem_biUnion.mpr ⟨v,va,Finset.mem_filter.mpr ⟨ba,vb⟩⟩
    have bound := Nat.mul_le_mul_left 6 ((Finset.card_le_card covers).trans Finset.card_biUnion_le)
    rw [Finset.mul_sum] at bound
    have total := Finset.sum_le_sum (s := support a) (fun v _ => cap v)
    simpa [size a (subM ha)] using bound.trans total
  refine ⟨M,subM,pairwise,?_⟩
  have bound := Nat.mul_le_mul_left 6 ((Finset.card_le_card cover).trans Finset.card_biUnion_le)
  rw [Finset.mul_sum] at bound
  have total := Finset.sum_le_sum (s := M) localBound
  simpa [mul_comm] using bound.trans total

end SteinerSail
