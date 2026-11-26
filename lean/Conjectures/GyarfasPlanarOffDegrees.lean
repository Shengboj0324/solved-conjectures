import Conjectures.GyarfasPlanarDirections

/-! Starting from heights zero through k−1, replacing height one removes the
pair 0,1 and adding height 2k−3 contributes exactly the pair k−2,k−1. -/

namespace GyarfasPlanar

private def initial (k i : ℕ) := (Finset.range (k-i)).erase i
private def afterRemoval (k i : ℕ) :=
  if i≤1 then (initial k i).erase (1-i) else initial k i
private def extraPair (k i : ℕ) : Finset ℕ :=
  if k-2 ≤ i then {2*k-3-i} else ∅

private theorem merged_eq {k i : ℕ} (hk : 8 ≤ k) (hi : i<k) (odd : Bool) :
    merged k odd i=afterRemoval k i ∪ extraPair k i := by
  ext j
  simp only [merged,Finset.mem_filter,Finset.mem_erase,Finset.mem_range,heights_mem,
    Finset.mem_union,afterRemoval,initial,extraPair]
  split_ifs <;> simp only [Finset.mem_erase,Finset.mem_range,Finset.mem_singleton,Finset.notMem_empty,
    or_false] <;> omega

private theorem initial_card {k i : ℕ} (hi : i<k) :
    (initial k i).card=k-i-(if i ≤ (k-1)/2 then 1 else 0) := by
  unfold initial
  split_ifs with h
  · rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)),Finset.card_range]
  · rw [Finset.erase_eq_of_notMem (by simp; omega),Finset.card_range,Nat.sub_zero]

private theorem removed_card {k i : ℕ} (hk : 8 ≤ k) :
    (afterRemoval k i).card=(initial k i).card-(if i≤1 then 1 else 0) := by
  unfold afterRemoval
  split_ifs with h
  · apply Finset.card_erase_of_mem
    exact Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr (by omega)⟩
  · omega

private theorem extra_disjoint {k i : ℕ} (hk : 8 ≤ k) (hi : i<k) :
    Disjoint (afterRemoval k i) (extraPair k i) := by
  apply Finset.disjoint_left.mpr
  intro j hj he
  have base : j∈initial k i := by
    unfold afterRemoval at hj
    split at hj
    · exact (Finset.mem_erase.mp hj).2
    · exact hj
  have low : j<k-i := Finset.mem_range.mp (Finset.mem_erase.mp base).2
  unfold extraPair at he
  split at he
  · have eq := Finset.mem_singleton.mp he
    omega
  · exact Finset.notMem_empty _ he

theorem merged_count {k i : ℕ} (hk : 8 ≤ k) (hi : i<k) (odd : Bool) :
    (merged k odd i).card=k-i-(if i ≤ (k-1)/2 then 1 else 0)-
      (if i≤1 then 1 else 0)+(if k-2 ≤ i then 1 else 0) := by
  have extra : (extraPair k i).card=(if k-2 ≤ i then 1 else 0) := by
    unfold extraPair
    by_cases h : k-2 ≤ i <;> simp [h]
  rw [merged_eq hk hi,Finset.card_union_of_disjoint (extra_disjoint hk hi),
    removed_card hk,initial_card hi,extra]

def offDegree (k : ℕ) (odd : Bool) (i : ℕ) :=
  k+odd.toNat-1+i+(if i ≤ (k-1)/2 then 1 else 0)+(if i≤1 then 1 else 0)-
    (if k-2 ≤ i then 1 else 0)

theorem off_degree {k i : ℕ} (hk : 8 ≤ k) (hi : i<k) (odd : Bool) :
    (directions (configuration k odd) (offAxis i)).card=offDegree k odd i := by
  have h := off_degree_sum hk hi odd
  rw [merged_count hk hi] at h
  unfold offDegree
  split_ifs at h ⊢ <;> omega

end GyarfasPlanar
