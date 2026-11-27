import Conjectures.DukesRevstackFiniteRows000To007

/-! Exact Eulerian and reduced revstack coefficient rows at orders 8 through 15. -/

namespace DukesRevstack.FiniteData

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

def e008 : Array ℤ := #[
  1, 247, 4293, 15619, 15619, 4293, 247, 1, 0]

theorem e008_eq : e008 = eulerRows 8 := calc
  e008 = nextEulerRow 7 e007 := by decide +kernel
  _ = eulerRows 8 := congrArg (nextEulerRow 7) e007_eq

def p008 : List ℤ := [
  1, 246, 4278, 15563, 15563, 4278, 246, 1]

theorem p008_eq : p008 = reducedRow 8 := calc
  p008 = combineRows 8 e008 e003 e004 := by decide +kernel
  _ = reducedRow 8 := by rw [e008_eq,e003_eq,e004_eq]; rfl

def e009 : Array ℤ := #[
  1, 502, 14608, 88234, 156190, 88234, 14608, 502, 1, 0]

theorem e009_eq : e009 = eulerRows 9 := calc
  e009 = nextEulerRow 8 e008 := by decide +kernel
  _ = eulerRows 9 := congrArg (nextEulerRow 8) e008_eq

def p009 : List ℤ := [
  1, 501, 14586, 88091, 155946, 88091, 14586, 501, 1]

theorem p009_eq : p009 = reducedRow 9 := calc
  p009 = combineRows 9 e009 e004 e004 := by decide +kernel
  _ = reducedRow 9 := by rw [e009_eq,e004_eq]; rfl

def e010 : Array ℤ := #[
  1, 1013, 47840, 455192, 1310354, 1310354, 455192, 47840, 1013, 1, 0]

theorem e010_eq : e010 = eulerRows 10 := calc
  e010 = nextEulerRow 9 e009 := by decide +kernel
  _ = eulerRows 10 := congrArg (nextEulerRow 9) e009_eq

def p010 : List ℤ := [
  1, 1012, 47803, 454829, 1309315, 1309315, 454829, 47803, 1012, 1]

theorem p010_eq : p010 = reducedRow 10 := calc
  p010 = combineRows 10 e010 e004 e005 := by decide +kernel
  _ = reducedRow 10 := by rw [e010_eq,e004_eq,e005_eq]; rfl

def e011 : Array ℤ := #[
  1, 2036, 152637, 2203488, 9738114, 15724248, 9738114, 2203488, 152637, 2036, 1, 0]

theorem e011_eq : e011 = eulerRows 11 := calc
  e011 = nextEulerRow 10 e010 := by decide +kernel
  _ = eulerRows 11 := congrArg (nextEulerRow 10) e010_eq

def p011 : List ℤ := [
  1, 2035, 152585, 2202680, 9734630, 15718538, 9734630, 2202680, 152585, 2035, 1]

theorem p011_eq : p011 = reducedRow 11 := calc
  p011 = combineRows 11 e011 e005 e005 := by decide +kernel
  _ = reducedRow 11 := by rw [e011_eq,e005_eq]; rfl

def e012 : Array ℤ := #[
  1, 4083, 478271, 10187685, 66318474, 162512286, 162512286, 66318474, 10187685, 478271, 4083, 1, 0]

theorem e012_eq : e012 = eulerRows 12 := calc
  e012 = nextEulerRow 11 e011 := by decide +kernel
  _ = eulerRows 12 := congrArg (nextEulerRow 11) e011_eq

def p012 : List ℤ := [
  1, 4082, 478188, 10185835, 66306532, 162482962, 162482962, 66306532, 10185835, 478188, 4082, 1]

theorem p012_eq : p012 = reducedRow 12 := calc
  p012 = combineRows 12 e012 e005 e006 := by decide +kernel
  _ = reducedRow 12 := by rw [e012_eq,e005_eq,e006_eq]; rfl

def e013 : Array ℤ := #[
  1, 8178, 1479726, 45533450, 423281535, 1505621508, 2275172004, 1505621508, 423281535, 45533450, 1479726,
  8178, 1, 0]

theorem e013_eq : e013 = eulerRows 13 := calc
  e013 = nextEulerRow 12 e012 := by decide +kernel
  _ = eulerRows 13 := congrArg (nextEulerRow 12) e012_eq

def p013 : List ℤ := [
  1, 8177, 1479612, 45529597, 423246503, 1505495762, 2274983096, 1505495762, 423246503, 45529597, 1479612,
  8177, 1]

theorem p013_eq : p013 = reducedRow 13 := calc
  p013 = combineRows 13 e013 e006 e006 := by decide +kernel
  _ = reducedRow 13 := by rw [e013_eq,e006_eq]; rfl

def e014 : Array ℤ := #[
  1, 16369, 4537314, 198410786, 2571742175, 12843262863, 27971176092, 27971176092, 12843262863, 2571742175,
  198410786, 4537314, 16369, 1, 0]

theorem e014_eq : e014 = eulerRows 14 := calc
  e014 = nextEulerRow 13 e013 := by decide +kernel
  _ = eulerRows 14 := congrArg (nextEulerRow 13) e013_eq

def p014 : List ℤ := [
  1, 16368, 4537137, 198402453, 2571635330, 12842727981, 27970011930, 27970011930, 12842727981, 2571635330,
  198402453, 4537137, 16368, 1]

theorem p014_eq : p014 = reducedRow 14 := calc
  p014 = combineRows 14 e014 e006 e007 := by decide +kernel
  _ = reducedRow 14 := by rw [e014_eq,e006_eq,e007_eq]; rfl

def e015 : Array ℤ := #[
  1, 32752, 13824739, 848090912, 15041229521, 102776998928, 311387598411, 447538817472, 311387598411,
  102776998928, 15041229521, 848090912, 13824739, 32752, 1, 0]

theorem e015_eq : e015 = eulerRows 15 := calc
  e015 = nextEulerRow 14 e014 := by decide +kernel
  _ = eulerRows 15 := congrArg (nextEulerRow 14) e014_eq

def p015 : List ℤ := [
  1, 32751, 13824499, 848074130, 15040938849, 102774998225, 311381557419, 447530114652, 311381557419,
  102774998225, 15040938849, 848074130, 13824499, 32751, 1]

theorem p015_eq : p015 = reducedRow 15 := calc
  p015 = combineRows 15 e015 e007 e007 := by decide +kernel
  _ = reducedRow 15 := by rw [e015_eq,e007_eq]; rfl

end DukesRevstack.FiniteData
