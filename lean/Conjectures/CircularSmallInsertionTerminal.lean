import Conjectures.CircularSmallInsertionFamily
import Mathlib.Data.Finset.Card

/-! At k=2g the two supports are consecutive intervals. Their matchings would
require 2g distinct nonzero lengths in a set of only 2g−1 possible lengths. -/

namespace CircularIndex.Insertion.Small

private theorem profile_length {n t : ℕ} {W L : List ℕ} (hm : L∈lengthProfiles n t W) :
    L.length=t := by
  induction t generalizing W L with
  | zero =>
    cases W with
    | nil => simp [lengthProfiles] at hm; simp [hm]
    | cons => simp [lengthProfiles] at hm
  | succ t ih =>
    cases W with
    | nil => simp [lengthProfiles] at hm
    | cons x xs =>
      obtain ⟨y,_,hy⟩ := List.mem_flatMap.mp hm
      obtain ⟨A,ha,rfl⟩ := List.mem_map.mp hy
      exact congrArg Nat.succ (ih ha)

theorem no_terminal_base {g : ℕ} (hg : 1≤g) (f : Fin 2 → ℕ → ℕ) : ¬ Base g (2*g) f := by
  intro base
  have prof (i : Fin 2) := lengthProfiles_complete (support_size (le_refl (2*g)) i.val)
    (support_nodup (by have := i.isLt; omega)) (base.matched i) (base.unique i)
  obtain ⟨A,hA,nA,sA⟩ := prof 0
  obtain ⟨B,hB,nB,sB⟩ := prof 1
  have nd : (A++B).Nodup := List.nodup_append.mpr ⟨nA,nB,by
    intro a ha b hb eq
    obtain ⟨x,hx,eh⟩ := sA a ha
    obtain ⟨y,hy,ef⟩ := sB b hb
    exact base.separated x hx y hy (eh.symm.trans (eq.trans ef))⟩
  have short (i : Fin 2) (x : ℕ) (hx : x∈support g (2*g) i.val) :
      1≤distance (vertexCount g) x (f i x) ∧ distance (vertexCount g) x (f i x)<2*g := by
    obtain ⟨hy,_,hne⟩ := base.matched i x hx
    simp [support,List.mem_range'_1] at hx hy
    unfold distance cyclicLength vertexCount
    omega
  have incl : (A++B).toFinset ⊆ (List.range' 1 (2*g-1)).toFinset := by
    intro a ha
    simp only [List.mem_toFinset,List.mem_append] at ha
    simp only [List.mem_toFinset,List.mem_range'_1]
    rcases ha with ha|ha
    · obtain ⟨x,hx,rfl⟩ := sA a ha
      have := short 0 x hx
      omega
    · obtain ⟨x,hx,rfl⟩ := sB a ha
      have := short 1 x hx
      omega
  have h := Finset.card_le_card incl
  rw [List.toFinset_card_of_nodup nd,List.toFinset_card_of_nodup (List.nodup_range' 1),
    List.length_range',List.length_append,profile_length hA,profile_length hB] at h
  omega

end CircularIndex.Insertion.Small
