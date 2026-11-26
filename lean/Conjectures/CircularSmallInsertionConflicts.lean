import Conjectures.CircularSmallInsertionTranslation
import Conjectures.CircularSmallInsertionFixtures

/-! All disjoint pairs of the forced blocks have one of the certified
cyclic differences. Every other pair shares an actual labelled edge. -/

namespace CircularIndex.Insertion.Small

set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

theorem conflicts_two : refChecks 0 forcedTwo=true := by decide +kernel
theorem conflicts_eight : refChecks 1 forcedEight=true := by decide +kernel

end CircularIndex.Insertion.Small
