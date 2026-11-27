import Conjectures.CircularSmallInsertionProfiles3
import Conjectures.CircularSmallInsertionPairings

/-! Complementary matchings for every possible base length set at g=5, k=3. -/

namespace CircularIndex.Insertion.Small.K3

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

private def result (_ : ℕ) : List (List (ℕ × ℕ) × List (ℕ × ℕ)) :=
  []

private theorem case0 : pairingsAt 5 3 61566=result 61566 := by decide +kernel

theorem viable : viablePairs 5 3=[] := by
  apply Eq.trans (viable_from_table (f := result) candidate_lengths ?_)
  · decide +kernel
  · intro s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    exact case0

end CircularIndex.Insertion.Small.K3
