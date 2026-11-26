import Conjectures.CircularSmallInsertionFixtures

/-! The surviving complementary pairs can be checked separately for each
possible base length set. -/

namespace CircularIndex.Insertion.Small

def pairingsAt (g k S : ℕ) :=
  (complements g k 0 S).flatMap fun left => (complements g k 1 S).map (fun right => (left,right))

theorem viable_from_table {g k : ℕ} {L : List ℕ} {f : ℕ → List (List (ℕ × ℕ) × List (ℕ × ℕ))}
    (lengths : lengthSets g k=L) (table : ∀ s∈L, pairingsAt g k s=f s) :
    viablePairs g k=(L.flatMap f).eraseDups := by
  change ((lengthSets g k).flatMap (pairingsAt g k)).eraseDups=_
  rw [lengths,List.flatMap_congr table]

end CircularIndex.Insertion.Small
