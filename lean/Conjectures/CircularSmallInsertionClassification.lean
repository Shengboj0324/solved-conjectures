import Conjectures.CircularSmallInsertionShapes2
import Conjectures.CircularSmallInsertionShapes3
import Conjectures.CircularSmallInsertionShapes4

/-! With a run of the first support anchored at zero, every window-valid
pair of at most two cyclic intervals is a member of the k-family or a reflection. -/

namespace CircularIndex.Insertion.Small.Shapes

theorem classify {g A B : ℕ} (hg₁ : 2≤g) (hg₂ : g≤4)
    (sha : TwoIntervals g A) (shb : TwoIntervals g B) (start : normalized g A=true)
    (h : WindowConditions g A B) : Equivalent g A B := by
  have hc : (windowPairs g).all (fun w => decide (Equivalent g w.1 w.2))=true := by
    interval_cases g
    · exact G2.checked
    · exact G3.checked
    · exact G4.checked
  exact of_decide_eq_true (List.all_eq_true.mp hc (A,B) (pairs_complete sha shb start h))

theorem count_window_pairs {g : ℕ} (hg₁ : 2≤g) (hg₂ : g≤4) : (windowPairs g).length=4*g := by
  interval_cases g
  · rw [G2.pairs_eq]
    decide
  · rw [G3.pairs_eq]
    decide
  · rw [G4.pairs_eq]
    decide

end CircularIndex.Insertion.Small.Shapes
