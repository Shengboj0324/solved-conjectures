import Conjectures.DukesRevstackRows

/-! Exact Eulerian and reduced revstack coefficient rows at orders 0 through 7. -/

namespace DukesRevstack.FiniteData

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

def e000 : Array ℤ := #[
  1]

theorem e000_eq : e000 = eulerRows 0 := rfl

def e001 : Array ℤ := #[
  1, 0]

theorem e001_eq : e001 = eulerRows 1 := calc
  e001 = nextEulerRow 0 e000 := by decide +kernel
  _ = eulerRows 1 := congrArg (nextEulerRow 0) e000_eq

def e002 : Array ℤ := #[
  1, 1, 0]

theorem e002_eq : e002 = eulerRows 2 := calc
  e002 = nextEulerRow 1 e001 := by decide +kernel
  _ = eulerRows 2 := congrArg (nextEulerRow 1) e001_eq

def e003 : Array ℤ := #[
  1, 4, 1, 0]

theorem e003_eq : e003 = eulerRows 3 := calc
  e003 = nextEulerRow 2 e002 := by decide +kernel
  _ = eulerRows 3 := congrArg (nextEulerRow 2) e002_eq

def p003 : List ℤ := [
  1, 3, 1]

theorem p003_eq : p003 = reducedRow 3 := calc
  p003 = combineRows 3 e003 e001 e001 := by decide +kernel
  _ = reducedRow 3 := by rw [e003_eq,e001_eq]; rfl

def e004 : Array ℤ := #[
  1, 11, 11, 1, 0]

theorem e004_eq : e004 = eulerRows 4 := calc
  e004 = nextEulerRow 3 e003 := by decide +kernel
  _ = eulerRows 4 := congrArg (nextEulerRow 3) e003_eq

def p004 : List ℤ := [
  1, 10, 10, 1]

theorem p004_eq : p004 = reducedRow 4 := calc
  p004 = combineRows 4 e004 e001 e002 := by decide +kernel
  _ = reducedRow 4 := by rw [e004_eq,e001_eq,e002_eq]; rfl

def e005 : Array ℤ := #[
  1, 26, 66, 26, 1, 0]

theorem e005_eq : e005 = eulerRows 5 := calc
  e005 = nextEulerRow 4 e004 := by decide +kernel
  _ = eulerRows 5 := congrArg (nextEulerRow 4) e004_eq

def p005 : List ℤ := [
  1, 25, 64, 25, 1]

theorem p005_eq : p005 = reducedRow 5 := calc
  p005 = combineRows 5 e005 e002 e002 := by decide +kernel
  _ = reducedRow 5 := by rw [e005_eq,e002_eq]; rfl

def e006 : Array ℤ := #[
  1, 57, 302, 302, 57, 1, 0]

theorem e006_eq : e006 = eulerRows 6 := calc
  e006 = nextEulerRow 5 e005 := by decide +kernel
  _ = eulerRows 6 := congrArg (nextEulerRow 5) e005_eq

def p006 : List ℤ := [
  1, 56, 297, 297, 56, 1]

theorem p006_eq : p006 = reducedRow 6 := calc
  p006 = combineRows 6 e006 e002 e003 := by decide +kernel
  _ = reducedRow 6 := by rw [e006_eq,e002_eq,e003_eq]; rfl

def e007 : Array ℤ := #[
  1, 120, 1191, 2416, 1191, 120, 1, 0]

theorem e007_eq : e007 = eulerRows 7 := calc
  e007 = nextEulerRow 6 e006 := by decide +kernel
  _ = eulerRows 7 := congrArg (nextEulerRow 6) e006_eq

def p007 : List ℤ := [
  1, 119, 1183, 2398, 1183, 119, 1]

theorem p007_eq : p007 = reducedRow 7 := calc
  p007 = combineRows 7 e007 e003 e003 := by decide +kernel
  _ = reducedRow 7 := by rw [e007_eq,e003_eq]; rfl

end DukesRevstack.FiniteData
