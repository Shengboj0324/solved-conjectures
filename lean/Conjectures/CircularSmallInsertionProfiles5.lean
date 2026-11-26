import Conjectures.CircularSmallInsertionSearch

/-! Checked base-length sets at g=5 and k=5. Each decimal integer represents
the set of lengths given by its nonzero binary digits. -/

namespace CircularIndex.Insertion.Small.K5

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

private def profile0 : List ℕ := [
  57350, 53254, 57354, 53258, 57362, 45062, 16414, 32798, 57356, 53260, 57364,
  45068, 28678, 45066, 28684, 8222, 57368, 28682, 53268, 53266, 45074, 45076,
  53272, 28690, 26630, 51206, 38918, 43018, 43014, 51212, 43020, 22534, 51210,
  26634, 63488]

private theorem checked0 : profiles 5 5 0=profile0 := by decide +kernel

private def profile1 : List ℕ := [
  57350, 45062, 51206, 57362, 57354, 53258, 45066, 43014, 51210, 53266, 28678,
  53254, 8222, 32798, 57356, 53260, 57364, 28684, 51212, 16414, 53272, 26634,
  43020, 43018, 45068, 53268, 57368, 28690, 45076, 45074, 26630, 28682, 22534,
  38918, 63488]

private theorem checked1 : profiles 5 5 1=profile1 := by decide +kernel

theorem candidate_lengths : lengthSets 5 5=[] := by
  unfold lengthSets
  rw [checked0,checked1]
  decide +kernel

end CircularIndex.Insertion.Small.K5
