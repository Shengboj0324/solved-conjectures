import Conjectures.CircularSmallInsertionFixtures
import Conjectures.CircularSmallInsertionViable1
import Conjectures.CircularSmallInsertionViable2
import Conjectures.CircularSmallInsertionViable3
import Conjectures.CircularSmallInsertionViable4
import Conjectures.CircularSmallInsertionViable5
import Conjectures.CircularSmallInsertionViable6
import Conjectures.CircularSmallInsertionViable7
import Conjectures.CircularSmallInsertionViable8
import Conjectures.CircularSmallInsertionViable9
import Mathlib.Tactic.IntervalCases

/-! For g=2,3,4 no complementary pair exists. For g=5 only k=2 and
k=8 survive, with one uniquely determined pair of complementary matchings
in each case. The checked computations use the published support intervals. -/

namespace CircularIndex.Insertion.Small

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

theorem viable_two : viablePairs 5 2=[forcedTwo] := K2.viable
theorem viable_eight : viablePairs 5 8=[forcedEight] := K8.viable

theorem viable_five (k : ℕ) (h₁ : 1≤k) (h₂ : k≤9) :
    viablePairs 5 k=if k=2 then [forcedTwo] else if k=8 then [forcedEight] else [] := by
  interval_cases k
  · exact K1.viable
  · exact K2.viable
  · exact K3.viable
  · exact K4.viable
  · exact K5.viable
  · exact K6.viable
  · exact K7.viable
  · exact K8.viable
  · exact K9.viable

theorem viable_small {g k : ℕ} (hg₁ : 2≤g) (hg₂ : g≤4) (hk₁ : 1≤k) (hk₂ : k<2*g) :
    viablePairs g k=[] := by
  interval_cases g <;> interval_cases k <;> decide +kernel

end CircularIndex.Insertion.Small
