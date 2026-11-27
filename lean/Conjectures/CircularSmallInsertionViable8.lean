import Conjectures.CircularSmallInsertionProfiles8
import Conjectures.CircularSmallInsertionPairings

/-! Complementary matchings for every possible base length set at g=5, k=8. -/

namespace CircularIndex.Insertion.Small.K8

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

private def result (s : ℕ) : List (List (ℕ × ℕ) × List (ℕ × ℕ)) :=
  if s=59638 then [forcedEight] else []

private theorem case0 : pairingsAt 5 8 61566=result 61566 := by decide +kernel
private theorem case1 : pairingsAt 5 8 61630=result 61630 := by decide +kernel
private theorem case2 : pairingsAt 5 8 59518=result 59518 := by decide +kernel
private theorem case3 : pairingsAt 5 8 55422=result 55422 := by decide +kernel
private theorem case4 : pairingsAt 5 8 47230=result 47230 := by decide +kernel
private theorem case5 : pairingsAt 5 8 61662=result 61662 := by decide +kernel
private theorem case6 : pairingsAt 5 8 30846=result 30846 := by decide +kernel
private theorem case7 : pairingsAt 5 8 61678=result 61678 := by decide +kernel
private theorem case8 : pairingsAt 5 8 61686=result 61686 := by decide +kernel
private theorem case9 : pairingsAt 5 8 61690=result 61690 := by decide +kernel
private theorem case10 : pairingsAt 5 8 59582=result 59582 := by decide +kernel
private theorem case11 : pairingsAt 5 8 59614=result 59614 := by decide +kernel
private theorem case12 : pairingsAt 5 8 55486=result 55486 := by decide +kernel
private theorem case13 : pairingsAt 5 8 30910=result 30910 := by decide +kernel
private theorem case14 : pairingsAt 5 8 47294=result 47294 := by decide +kernel
private theorem case15 : pairingsAt 5 8 59630=result 59630 := by decide +kernel
private theorem case16 : pairingsAt 5 8 59638=result 59638 := by decide +kernel
private theorem case17 : pairingsAt 5 8 55518=result 55518 := by decide +kernel
private theorem case18 : pairingsAt 5 8 47326=result 47326 := by decide +kernel

theorem viable : viablePairs 5 8=[forcedEight] := by
  apply Eq.trans (viable_from_table (f := result) candidate_lengths ?_)
  · decide +kernel
  · intro s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact case0
    · exact case1
    · exact case2
    · exact case3
    · exact case4
    · exact case5
    · exact case6
    · exact case7
    · exact case8
    · exact case9
    · exact case10
    · exact case11
    · exact case12
    · exact case13
    · exact case14
    · exact case15
    · exact case16
    · exact case17
    · exact case18

end CircularIndex.Insertion.Small.K8
