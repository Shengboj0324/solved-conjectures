import Conjectures.CircularSmallInsertionProfiles1
import Conjectures.CircularSmallInsertionPairings

/-! Complementary matchings for every possible base length set at g=5, k=1. -/

namespace CircularIndex.Insertion.Small.K1

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

private def result (_ : ℕ) : List (List (ℕ × ℕ) × List (ℕ × ℕ)) :=
  []

private theorem case0 : pairingsAt 5 1 37374=result 37374 := by decide +kernel
private theorem case1 : pairingsAt 5 1 25086=result 25086 := by decide +kernel
private theorem case2 : pairingsAt 5 1 41470=result 41470 := by decide +kernel
private theorem case3 : pairingsAt 5 1 49662=result 49662 := by decide +kernel
private theorem case4 : pairingsAt 5 1 35326=result 35326 := by decide +kernel
private theorem case5 : pairingsAt 5 1 20990=result 20990 := by decide +kernel

theorem viable : viablePairs 5 1=[] := by
  apply Eq.trans (viable_from_table (f := result) candidate_lengths ?_)
  · decide +kernel
  · intro s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
    · exact case0
    · exact case1
    · exact case2
    · exact case3
    · exact case4
    · exact case5

end CircularIndex.Insertion.Small.K1
