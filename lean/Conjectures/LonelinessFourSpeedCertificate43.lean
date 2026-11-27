import Conjectures.LonelinessFourSpeedCertificate

/-! Exhaustive support certificate modulo 43, at threshold 2/9.
Generated finite data are accepted only through ordinary kernel reduction. -/

namespace Loneliness.Modular.FourSpeed.Prime43

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def inverse (a : ℕ) : ℕ := ([0,1,22,29,11,26,36,37,27,24,13,4,18,10,40,23,35,38,12,34,28,41,2,15,9,31,5,8,20,3,33,25,39,30,19,16,6,7,17,32,14,21,42] : List ℕ).getD a 0

def retained : Finset (Finset ℕ) :=
  {{1,2,3,4},
  {1,2,3,8},
  {1,2,3,12},
  {1,2,20,21},
  {1,3,4,5},
  {1,3,4,7},
  {1,3,4,14},
  {1,3,9,12},
  {1,3,11,12},
  {1,3,16,17},
  {1,3,18,19},
  {1,4,5,6},
  {1,4,5,9},
  {1,4,19,20},
  {1,5,6,7},
  {1,8,9,10}}

theorem inverse_finite : ∀ a : Fin 22, 0<a.val →
    (a.val*inverse a.val)%43=1%43 := by decide +kernel

theorem inverse_correct (a : ℕ) (ha : 0<a) (hbound : 2*a≤43) :
    (a*inverse a)%43=1%43 :=
  inverse_finite ⟨a,by omega⟩ ha

theorem retained_card : ∀ s∈retained, s.card=4 := by decide +kernel

theorem rows1_checked : residueCheck 2 9 43 1 inverse retained=true := by decide +kernel

theorem rows2_checked : residueCheck 2 9 43 2 inverse retained=true := by decide +kernel

theorem rows3_checked : residueCheck 2 9 43 3 inverse retained=true := by decide +kernel

/-! The four-element rows are checked in six pieces, split by the sum of the
support modulo six. One decision over all of them exceeds the CI memory cap. -/

theorem rows4_part0 : ∀ s∈(boundedSupports 43 4).filter (fun s => s.sum id % 6=0),
    PairNormalized 43 inverse s → rowCheck 2 9 43 retained s=true := by decide +kernel

theorem rows4_part1 : ∀ s∈(boundedSupports 43 4).filter (fun s => s.sum id % 6=1),
    PairNormalized 43 inverse s → rowCheck 2 9 43 retained s=true := by decide +kernel

theorem rows4_part2 : ∀ s∈(boundedSupports 43 4).filter (fun s => s.sum id % 6=2),
    PairNormalized 43 inverse s → rowCheck 2 9 43 retained s=true := by decide +kernel

theorem rows4_part3 : ∀ s∈(boundedSupports 43 4).filter (fun s => s.sum id % 6=3),
    PairNormalized 43 inverse s → rowCheck 2 9 43 retained s=true := by decide +kernel

theorem rows4_part4 : ∀ s∈(boundedSupports 43 4).filter (fun s => s.sum id % 6=4),
    PairNormalized 43 inverse s → rowCheck 2 9 43 retained s=true := by decide +kernel

theorem rows4_part5 : ∀ s∈(boundedSupports 43 4).filter (fun s => s.sum id % 6=5),
    PairNormalized 43 inverse s → rowCheck 2 9 43 retained s=true := by decide +kernel

theorem rows4_checked : residueCheck 2 9 43 4 inverse retained=true :=
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
    residueCheck 2 9 43 r inverse retained=true := by
  have hcases : r=1 ∨ r=2 ∨ r=3 ∨ r=4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact rows1_checked
  · exact rows2_checked
  · exact rows3_checked
  · exact rows4_checked

theorem residue_cover (ds : List ℕ) (hne : ds≠[]) (hlen : ds.length≤4)
    (hmod : ∀ d∈ds, d%43≠0) (hlow : value ds<(2/9 : ℝ)) :
    ∃ u v : ℕ, (u*v)%43=1%43 ∧ foldedSupport 43 u (residueSupport 43 ds)∈retained :=
  checked_residue_cover (num:=2) (den:=9) (m:=43) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) inverse inverse_correct retained all_rows_checked ds hne hlen hmod hlow

end Loneliness.Modular.FourSpeed.Prime43
