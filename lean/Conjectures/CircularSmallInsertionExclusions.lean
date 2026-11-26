import Conjectures.CircularSmallInsertionCertificates
import Conjectures.CircularSmallInsertionConflicts
import Conjectures.CircularSmallInsertionPositive

/-! Classification of individual forward insertions for the small parameters,
and exclusion of three pairwise edge-disjoint forward insertions at g=5. -/

namespace CircularIndex.Insertion.Small

private theorem viable_of_forward {g k c : ℕ} (hk : k≤2*g) (H : OneForward g k c) :
    ∃ M, M∈viablePairs g k := by
  obtain ⟨f,base,h,hw⟩ := H
  obtain ⟨h₀,p₀,a₀⟩ := window_supplies hk hw 0
  obtain ⟨h₁,p₁,a₁⟩ := window_supplies hk hw 1
  obtain ⟨M,hm,_⟩ := viablePairs_complete hk base p₀ a₀ p₁ a₁
  exact ⟨M,hm⟩

theorem no_forward_small {g k : ℕ} (hg₁ : 2≤g) (hg₂ : g≤4)
    (hk₁ : 1≤k) (hk₂ : k<2*g) (c : ℕ) : ¬ OneForward g k c := by
  intro H
  obtain ⟨M,hm⟩ := viable_of_forward (by omega) H
  rw [viable_small hg₁ hg₂ hk₁ hk₂] at hm
  exact List.not_mem_nil hm

theorem forward_five_iff {k : ℕ} (hk₁ : 1≤k) (hk₂ : k<10) (c : ℕ) :
    OneForward 5 k c ↔ k=2 ∨ k=8 := by
  constructor
  · intro H
    obtain ⟨M,hm⟩ := viable_of_forward (by omega) H
    rw [viable_five k hk₁ (by omega)] at hm
    by_contra! fail
    simp [fail.1,fail.2] at hm
  · rintro (rfl|rfl)
    · exact forward_two c
    · exact forward_eight c

private theorem three_forces_cycle {k q : ℕ} (hk : k≤10) (hq : q<2)
    {M : MatchPair} (only : viablePairs 5 k=[M]) (checked : refChecks q M=true)
    (cs : Fin 3 → Fin (2*vertexCount 5)) : ¬ ThreeForward 5 k cs := by
  rintro ⟨f,base,h,ad,dis⟩
  have separate (i j : Fin 3) (hij : i≠j) (e : ℕ × ℕ)
      (he : e∈forcedBlock 5 (cs i).val M) (he' : e∈forcedBlock 5 (cs j).val M) : False :=
    dis i j hij e ((forced_window hk base only (ad i) e).mp he)
      ((forced_window hk base only (ad j) e).mp he')
  exact no_gap_triangle hq (cs 0) (cs 1) (cs 2)
    (disjoint_gap checked _ _ (separate 0 1 (by decide)))
    (disjoint_gap checked _ _ (separate 1 2 (by decide)))
    (disjoint_gap checked _ _ (separate 2 0 (by decide)))

private theorem one_of_three {g k : ℕ} {cs : Fin 3 → Fin (2*vertexCount g)}
    (H : ThreeForward g k cs) : OneForward g k (cs 0).val := by
  obtain ⟨f,base,h,hw,_⟩ := H
  exact ⟨f,base,h 0,hw 0⟩

theorem no_three_forward_small {g k : ℕ} (hg₁ : 2≤g) (hg₂ : g≤4) (hk₁ : 1≤k) (hk₂ : k<2*g)
    (cs : Fin 3 → Fin (2*vertexCount g)) : ¬ ThreeForward g k cs :=
  fun H => no_forward_small hg₁ hg₂ hk₁ hk₂ _ (one_of_three H)

theorem no_three_forward_five {k : ℕ} (hk₁ : 1≤k) (hk₂ : k<10)
    (cs : Fin 3 → Fin (2*vertexCount 5)) : ¬ ThreeForward 5 k cs := by
  intro H
  rcases (forward_five_iff hk₁ hk₂ _).mp (one_of_three H) with rfl|rfl
  · exact three_forces_cycle (by decide) (by decide) viable_two conflicts_two cs H
  · exact three_forces_cycle (by decide) (by decide) viable_eight conflicts_eight cs H

end CircularIndex.Insertion.Small
