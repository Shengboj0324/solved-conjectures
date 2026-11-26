import Conjectures.CircularSmallInsertionWindows

/-! The two complementary matchings forced at each viable support of the
31-vertex forward insertion problem. -/

namespace CircularIndex.Insertion.Small

def forcedTwo : List (ℕ × ℕ) × List (ℕ × ℕ) :=
  ([(0,19),(1,20),(13,16),(14,17),(15,18)],[(1,13),(2,14),(15,18),(16,19),(17,20)])

def forcedEight : List (ℕ × ℕ) × List (ℕ × ℕ) :=
  ([(0,19),(1,20),(2,5),(3,6),(4,7)],[(1,4),(2,5),(3,6),(7,19),(8,20)])

end CircularIndex.Insertion.Small
