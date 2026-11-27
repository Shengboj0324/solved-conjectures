import Conjectures.CircularSmallInsertionProfiles5
import Conjectures.CircularSmallInsertionPairings

/-! Complementary matchings for every possible base length set at g=5, k=5. -/

namespace CircularIndex.Insertion.Small.K5

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

private def result (_ : ℕ) : List (List (ℕ × ℕ) × List (ℕ × ℕ)) :=
  []


theorem viable : viablePairs 5 5=[] := by
  apply Eq.trans (viable_from_table (f := result) candidate_lengths ?_)
  · decide +kernel
  · intro s hs
    exact False.elim (List.not_mem_nil hs)

end CircularIndex.Insertion.Small.K5
