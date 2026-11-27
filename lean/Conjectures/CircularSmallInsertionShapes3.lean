import Conjectures.CircularSmallInsertionShapes
import Mathlib.Tactic.IntervalCases

/-! All normalized window-valid pairs of two cyclic intervals at g=3. -/

namespace CircularIndex.Insertion.Small.Shapes.G3

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

private def row0 : List ℕ := [63, 3969, 7937, 507905, 3843, 7683, 491523, 3591, 7175, 458759, 3087,
  6159, 393231, 2079, 4127, 262175]
private theorem start0 : atStart 3 0=row0 := by decide +kernel

private def row1 : List ℕ := [126, 7938, 15874, 491523, 7686, 15366, 458759, 7182, 14350, 393231, 6174,
  12318, 262175, 63, 4158, 8254]
private theorem start1 : atStart 3 1=row1 := by decide +kernel

private def row2 : List ℕ := [252, 15876, 31748, 458759, 15372, 30732, 393231, 14364, 28700, 262175, 63,
  12348, 24636, 126, 8316, 16508]
private theorem start2 : atStart 3 2=row2 := by decide +kernel

private def row3 : List ℕ := [504, 31752, 63496, 393231, 30744, 61464, 262175, 63, 28728, 57400, 126,
  24696, 49272, 252, 16632, 33016]
private theorem start3 : atStart 3 3=row3 := by decide +kernel

private def row4 : List ℕ := [1008, 63504, 126992, 262175, 63, 61488, 122928, 126, 57456, 114800, 252,
  49392, 98544, 504, 33264, 66032]
private theorem start4 : atStart 3 4=row4 := by decide +kernel

private def row5 : List ℕ := [63, 2016, 127008, 253984, 126, 122976, 245856, 252, 114912, 229600, 504,
  98784, 197088, 1008, 66528, 132064]
private theorem start5 : atStart 3 5=row5 := by decide +kernel

private def row6 : List ℕ := [126, 4032, 254016, 507968, 252, 245952, 491712, 504, 229824, 459200, 1008,
  197568, 394176, 2016, 133056, 264128]
private theorem start6 : atStart 3 6=row6 := by decide +kernel

private def row7 : List ℕ := [252, 8064, 508032, 491649, 504, 491904, 459137, 1008, 459648, 394113, 2016,
  395136, 264065, 3969, 4032, 266112]
private theorem start7 : atStart 3 7=row7 := by decide +kernel

private def row8 : List ℕ := [504, 16128, 491777, 459011, 1008, 459521, 393987, 2016, 395009, 263939, 3843,
  4032, 265985, 7937, 7938, 8064]
private theorem start8 : atStart 3 8=row8 := by decide +kernel

private def row9 : List ℕ := [1008, 32256, 459267, 393735, 2016, 394755, 263687, 3591, 4032, 265731, 7683,
  7686, 8064, 15874, 15876, 16128]
private theorem start9 : atStart 3 9=row9 := by decide +kernel

private def row10 : List ℕ := [2016, 64512, 394247, 263183, 3087, 4032, 265223, 7175, 7182, 8064, 15366,
  15372, 16128, 31748, 31752, 32256]
private theorem start10 : atStart 3 10=row10 := by decide +kernel

private def row11 : List ℕ := [2079, 4032, 129024, 264207, 6159, 6174, 8064, 14350, 14364, 16128, 30732,
  30744, 32256, 63496, 63504, 64512]
private theorem start11 : atStart 3 11=row11 := by decide +kernel

private def row12 : List ℕ := [4127, 4158, 8064, 258048, 12318, 12348, 16128, 28700, 28728, 32256, 61464,
  61488, 64512, 126992, 127008, 129024]
private theorem start12 : atStart 3 12=row12 := by decide +kernel

private def row13 : List ℕ := [8254, 8316, 16128, 516096, 24636, 24696, 32256, 57400, 57456, 64512, 122928,
  122976, 129024, 253984, 254016, 258048]
private theorem start13 : atStart 3 13=row13 := by decide +kernel

private def row14 : List ℕ := [16508, 16632, 32256, 507905, 49272, 49392, 64512, 114800, 114912, 129024, 245856,
  245952, 258048, 507968, 508032, 516096]
private theorem start14 : atStart 3 14=row14 := by decide +kernel

private def row15 : List ℕ := [33016, 33264, 64512, 491523, 98544, 98784, 129024, 229600, 229824, 258048, 491712,
  491904, 516096, 491649, 491777, 507905]
private theorem start15 : atStart 3 15=row15 := by decide +kernel

private def row16 : List ℕ := [66032, 66528, 129024, 458759, 197088, 197568, 258048, 459200, 459648, 516096, 459137,
  459521, 507905, 459011, 459267, 491523]
private theorem start16 : atStart 3 16=row16 := by decide +kernel

private def row17 : List ℕ := [132064, 133056, 258048, 393231, 394176, 395136, 516096, 394113, 395009, 507905, 393987,
  394755, 491523, 393735, 394247, 458759]
private theorem start17 : atStart 3 17=row17 := by decide +kernel

private def row18 : List ℕ := [262175, 264128, 266112, 516096, 264065, 265985, 507905, 263939, 265731, 491523, 263687,
  265223, 458759, 263183, 264207, 393231]
private theorem start18 : atStart 3 18=row18 := by decide +kernel

private def supports : List ℕ := [63, 3969, 7937, 507905, 3843, 7683, 491523, 3591, 7175, 458759, 3087,
  6159, 393231, 2079, 4127, 262175, 126, 7938, 15874, 7686, 15366, 7182,
  14350, 6174, 12318, 4158, 8254, 252, 15876, 31748, 15372, 30732, 14364,
  28700, 12348, 24636, 8316, 16508, 504, 31752, 63496, 30744, 61464, 28728,
  57400, 24696, 49272, 16632, 33016, 1008, 63504, 126992, 61488, 122928, 57456,
  114800, 49392, 98544, 33264, 66032, 2016, 127008, 253984, 122976, 245856, 114912,
  229600, 98784, 197088, 66528, 132064, 4032, 254016, 507968, 245952, 491712, 229824,
  459200, 197568, 394176, 133056, 264128, 8064, 508032, 491649, 491904, 459137, 459648,
  394113, 395136, 264065, 266112, 16128, 491777, 459011, 459521, 393987, 395009, 263939,
  265985, 32256, 459267, 393735, 394755, 263687, 265731, 64512, 394247, 263183, 265223,
  129024, 264207, 258048, 516096]

private def certified (s : Fin (vertexCount 3)) : List ℕ :=
  [row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18][s.val]?.getD []

private theorem table (s : Fin (vertexCount 3)) : atStart 3 s.val=certified s := by
  rcases s with ⟨i,hi⟩
  change i<19 at hi
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
  · exact start13
  · exact start14
  · exact start15
  · exact start16
  · exact start17
  · exact start18

private theorem supports_eq : allSupports 3=supports := by
  unfold allSupports
  rw [show (fun s : Fin (vertexCount 3) => atStart 3 s.val)=certified from funext table]
  decide +kernel

theorem pairs_eq : windowPairs 3=[(63,63), (63,126), (3969,7937), (7937,7938), (3843,7683), (7683,7686), (3591,7175), (7175,7182), (3087,6159), (6159,6174), (2079,4127),
  (4127,4158)] := by
  unfold windowPairs
  rw [supports_eq]
  decide +kernel

theorem checked : (windowPairs 3).all (fun w => decide (Equivalent 3 w.1 w.2))=true := by
  rw [pairs_eq]
  decide +kernel

end CircularIndex.Insertion.Small.Shapes.G3
