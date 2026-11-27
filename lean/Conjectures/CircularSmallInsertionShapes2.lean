import Conjectures.CircularSmallInsertionShapes
import Mathlib.Tactic.IntervalCases

/-! All normalized window-valid pairs of two cyclic intervals at g=2. -/

namespace CircularIndex.Insertion.Small.Shapes.G2

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

private def row0 : List ℕ := [15, 225, 449, 7169, 195, 387, 6147, 135, 263, 4103]
private theorem start0 : atStart 2 0=row0 := by decide +kernel

private def row1 : List ℕ := [30, 450, 898, 6147, 390, 774, 4103, 15, 270, 526]
private theorem start1 : atStart 2 1=row1 := by decide +kernel

private def row2 : List ℕ := [60, 900, 1796, 4103, 15, 780, 1548, 30, 540, 1052]
private theorem start2 : atStart 2 2=row2 := by decide +kernel

private def row3 : List ℕ := [15, 120, 1800, 3592, 30, 1560, 3096, 60, 1080, 2104]
private theorem start3 : atStart 2 3=row3 := by decide +kernel

private def row4 : List ℕ := [30, 240, 3600, 7184, 60, 3120, 6192, 120, 2160, 4208]
private theorem start4 : atStart 2 4=row4 := by decide +kernel

private def row5 : List ℕ := [60, 480, 7200, 6177, 120, 6240, 4193, 225, 240, 4320]
private theorem start5 : atStart 2 5=row5 := by decide +kernel

private def row6 : List ℕ := [120, 960, 6209, 4163, 195, 240, 4289, 449, 450, 480]
private theorem start6 : atStart 2 6=row6 := by decide +kernel

private def row7 : List ℕ := [135, 240, 1920, 4227, 387, 390, 480, 898, 900, 960]
private theorem start7 : atStart 2 7=row7 := by decide +kernel

private def row8 : List ℕ := [263, 270, 480, 3840, 774, 780, 960, 1796, 1800, 1920]
private theorem start8 : atStart 2 8=row8 := by decide +kernel

private def row9 : List ℕ := [526, 540, 960, 7680, 1548, 1560, 1920, 3592, 3600, 3840]
private theorem start9 : atStart 2 9=row9 := by decide +kernel

private def row10 : List ℕ := [1052, 1080, 1920, 7169, 3096, 3120, 3840, 7184, 7200, 7680]
private theorem start10 : atStart 2 10=row10 := by decide +kernel

private def row11 : List ℕ := [2104, 2160, 3840, 6147, 6192, 6240, 7680, 6177, 6209, 7169]
private theorem start11 : atStart 2 11=row11 := by decide +kernel

private def row12 : List ℕ := [4103, 4208, 4320, 7680, 4193, 4289, 7169, 4163, 4227, 6147]
private theorem start12 : atStart 2 12=row12 := by decide +kernel

private def supports : List ℕ := [15, 225, 449, 7169, 195, 387, 6147, 135, 263, 4103, 30,
  450, 898, 390, 774, 270, 526, 60, 900, 1796, 780, 1548,
  540, 1052, 120, 1800, 3592, 1560, 3096, 1080, 2104, 240, 3600,
  7184, 3120, 6192, 2160, 4208, 480, 7200, 6177, 6240, 4193, 4320,
  960, 6209, 4163, 4289, 1920, 4227, 3840, 7680]

private def certified (s : Fin (vertexCount 2)) : List ℕ :=
  [row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12][s.val]?.getD []

private theorem table (s : Fin (vertexCount 2)) : atStart 2 s.val=certified s := by
  rcases s with ⟨i,hi⟩
  change i<13 at hi
  interval_cases i
  · exact start0
  · exact start1
  · exact start2
  · exact start3
  · exact start4
  · exact start5
  · exact start6
  · exact start7
  · exact start8
  · exact start9
  · exact start10
  · exact start11
  · exact start12

private theorem supports_eq : allSupports 2=supports := by
  unfold allSupports
  rw [show (fun s : Fin (vertexCount 2) => atStart 2 s.val)=certified from funext table]
  decide +kernel

theorem pairs_eq : windowPairs 2=[(15,15), (15,30), (225,449), (449,450), (195,387), (387,390), (135,263), (263,270)] := by
  unfold windowPairs
  rw [supports_eq]
  decide +kernel

theorem checked : (windowPairs 2).all (fun w => decide (Equivalent 2 w.1 w.2))=true := by
  rw [pairs_eq]
  decide +kernel

end CircularIndex.Insertion.Small.Shapes.G2
