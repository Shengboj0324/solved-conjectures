import Conjectures.CircularSmallInsertionSearch

/-! Checked base-length sets at g=5 and k=6. Each decimal integer represents
the set of lengths given by its nonzero binary digits. -/

namespace CircularIndex.Insertion.Small.K6

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

private def profile0 : List ℕ := [
  49166, 40974, 61442, 24590, 36878, 20494, 49174, 40982, 49180, 24598, 61444,
  49178, 40986, 24604, 61448, 36886, 12310, 61456, 24602, 40988, 20506, 36892,
  36890, 20502, 49190, 40998, 49194, 49196, 24618, 41004, 41002, 24614, 20518,
  36902, 61472, 12302, 59394, 55298, 10254, 34830, 59396, 18446, 55304, 18454,
  34838, 59408, 55300, 59400, 30722, 47108, 47106]

private theorem checked0 : profiles 5 6 0=profile0 := by decide +kernel

private def profile1 : List ℕ := [
  24590, 36878, 49166, 40974, 59394, 12302, 18446, 34830, 40982, 20502, 40988,
  36886, 49174, 20494, 61444, 59396, 24602, 49178, 36890, 36892, 20506, 24604,
  61448, 10254, 59400, 34838, 18454, 24598, 40986, 49180, 12310, 61456, 59408,
  24614, 49190, 36902, 41002, 40998, 49196, 41004, 20518, 49194, 24618, 61472,
  61442, 47106, 55300, 47108, 55304, 55298, 30722]

private theorem checked1 : profiles 5 6 1=profile1 := by decide +kernel

theorem candidate_lengths : lengthSets 5 6=[] := by
  unfold lengthSets
  rw [checked0,checked1]
  decide +kernel

end CircularIndex.Insertion.Small.K6
