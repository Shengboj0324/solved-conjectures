import Conjectures.CircularSmallInsertionSearch

/-! Checked base-length sets at g=5 and k=4. Each decimal integer represents
the set of lengths given by its nonzero binary digits. -/

namespace CircularIndex.Insertion.Small.K4

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

private def profile0 : List ℕ := [
  24590, 40982, 40974, 49178, 49190, 36878, 49174, 36886, 40986, 40998, 49194,
  49166, 20494, 24598, 24604, 12310, 49180, 49196, 40988, 24602, 24618, 41004,
  41002, 20506, 36892, 36890, 61442, 61444, 24614, 61456, 20502, 61448, 12302,
  20518, 36902, 61472, 10254, 18454, 34830, 34838, 18446, 59394, 59396, 55298,
  55300, 59400, 55304, 59408, 30722, 47108, 47106]

private theorem checked0 : profiles 5 4 0=profile0 := by decide +kernel

private def profile1 : List ℕ := [
  12302, 20502, 36878, 24602, 24614, 40974, 18446, 49178, 49190, 49174, 34838,
  36890, 36902, 41002, 34830, 40986, 40998, 20494, 24598, 40982, 24590, 49196,
  36892, 41004, 18454, 20518, 24604, 49166, 10254, 12310, 40988, 49194, 49180,
  20506, 24618, 61444, 61442, 59394, 36886, 59396, 61448, 59400, 61456, 59408,
  61472, 55300, 55298, 47106, 47108, 55304, 30722]

private theorem checked1 : profiles 5 4 1=profile1 := by decide +kernel

theorem candidate_lengths : lengthSets 5 4=[] := by
  unfold lengthSets
  rw [checked0,checked1]
  decide +kernel

end CircularIndex.Insertion.Small.K4
