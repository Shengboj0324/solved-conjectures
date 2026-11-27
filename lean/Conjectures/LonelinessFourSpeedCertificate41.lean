import Conjectures.LonelinessFourSpeedCertificate

/-! Exhaustive support certificate modulo 41, at threshold 2/9.
Generated finite data are accepted only through ordinary kernel reduction. -/

namespace Loneliness.Modular.FourSpeed.Prime41

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def inverse (a : ℕ) : ℕ := ([0,1,21,14,31,33,7,6,36,32,37,15,24,19,3,11,18,29,16,13,39,2,28,25,12,23,30,38,22,17,26,4,9,5,35,34,8,10,27,20,40] : List ℕ).getD a 0

def retained : Finset (Finset ℕ) :=
  {{1,2,3,4},
  {1,2,3,5},
  {1,2,3,8},
  {1,2,3,9},
  {1,2,3,12},
  {1,2,3,13},
  {1,2,3,16},
  {1,2,3,17},
  {1,2,3,20},
  {1,2,4,6},
  {1,2,7,17},
  {1,2,9,11},
  {1,2,11,12},
  {1,2,12,14},
  {1,2,12,17},
  {1,2,17,19},
  {1,2,19,20},
  {1,3,4,5},
  {1,3,4,7},
  {1,3,4,14},
  {1,3,9,10},
  {1,3,9,12},
  {1,3,9,14},
  {1,3,11,12},
  {1,3,14,17},
  {1,3,15,16},
  {1,3,16,17},
  {1,3,17,18},
  {1,4,5,6},
  {1,4,5,9},
  {1,4,18,19},
  {1,5,6,7},
  {1,5,6,11},
  {1,11,12,18}}

theorem inverse_finite : ∀ a : Fin 21, 0<a.val →
    (a.val*inverse a.val)%41=1%41 := by decide +kernel

theorem inverse_correct (a : ℕ) (ha : 0<a) (hbound : 2*a≤41) :
    (a*inverse a)%41=1%41 :=
  inverse_finite ⟨a,by omega⟩ ha

theorem retained_card : ∀ s∈retained, s.card=4 := by decide +kernel

theorem rows1_checked : residueCheck 2 9 41 1 inverse retained=true := by decide +kernel

theorem rows2_checked : residueCheck 2 9 41 2 inverse retained=true := by decide +kernel

theorem rows3_checked : residueCheck 2 9 41 3 inverse retained=true := by decide +kernel

/-! The four-element rows are checked in six pieces, split by the sum of the
support modulo six. One decision over all of them exceeds the CI memory cap. -/

theorem rows4_part0 : ∀ s∈(boundedSupports 41 4).filter (fun s => s.sum id % 6=0),
    PairNormalized 41 inverse s → rowCheck 2 9 41 retained s=true := by decide +kernel

theorem rows4_part1 : ∀ s∈(boundedSupports 41 4).filter (fun s => s.sum id % 6=1),
    PairNormalized 41 inverse s → rowCheck 2 9 41 retained s=true := by decide +kernel

theorem rows4_part2 : ∀ s∈(boundedSupports 41 4).filter (fun s => s.sum id % 6=2),
    PairNormalized 41 inverse s → rowCheck 2 9 41 retained s=true := by decide +kernel

theorem rows4_part3 : ∀ s∈(boundedSupports 41 4).filter (fun s => s.sum id % 6=3),
    PairNormalized 41 inverse s → rowCheck 2 9 41 retained s=true := by decide +kernel

theorem rows4_part4 : ∀ s∈(boundedSupports 41 4).filter (fun s => s.sum id % 6=4),
    PairNormalized 41 inverse s → rowCheck 2 9 41 retained s=true := by decide +kernel

theorem rows4_part5 : ∀ s∈(boundedSupports 41 4).filter (fun s => s.sum id % 6=5),
    PairNormalized 41 inverse s → rowCheck 2 9 41 retained s=true := by decide +kernel

theorem rows4_checked : residueCheck 2 9 41 4 inverse retained=true :=
  residueCheck_of_sum_chunks (by decide) 6 (by decide) fun i hi => by
    match i, hi with
    | 0, _ => exact rows4_part0
    | 1, _ => exact rows4_part1
    | 2, _ => exact rows4_part2
    | 3, _ => exact rows4_part3
    | 4, _ => exact rows4_part4
    | 5, _ => exact rows4_part5
    | _+6, h => omega


theorem all_rows_checked (r : ℕ) (hr : 0<r) (hbound : r≤4) :
    residueCheck 2 9 41 r inverse retained=true := by
  have hcases : r=1 ∨ r=2 ∨ r=3 ∨ r=4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact rows1_checked
  · exact rows2_checked
  · exact rows3_checked
  · exact rows4_checked

theorem residue_cover (ds : List ℕ) (hne : ds≠[]) (hlen : ds.length≤4)
    (hmod : ∀ d∈ds, d%41≠0) (hlow : value ds<(2/9 : ℝ)) :
    ∃ u v : ℕ, (u*v)%41=1%41 ∧ foldedSupport 41 u (residueSupport 41 ds)∈retained :=
  checked_residue_cover (num:=2) (den:=9) (m:=41) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) inverse inverse_correct retained all_rows_checked ds hne hlen hmod hlow

end Loneliness.Modular.FourSpeed.Prime41
