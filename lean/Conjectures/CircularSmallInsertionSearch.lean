import Conjectures.CircularSmallInsertionMatchings
import Mathlib.Data.Nat.Bitwise

/-! Exhaustive search for complementary perfect matchings on the two supports
of the cyclic q=3 base. The search covers every possible partner involution. -/

namespace CircularIndex.Insertion.Small

def support (g k ε : ℕ) : List ℕ :=
  List.range' ε k ++ List.range' (2*g+1+k) (2*g-k)

theorem support_size {g k : ℕ} (hk : k≤2*g) (ε : ℕ) : (support g k ε).length=2*g := by
  simp [support]
  omega

theorem support_nodup {g k ε : ℕ} (hε : ε≤1) : (support g k ε).Nodup := by
  rw [support,List.nodup_append]
  refine ⟨List.nodup_range' 1,List.nodup_range' 1,?_⟩
  intro x hx y hy eq
  simp only [List.mem_range'_1] at hx hy
  omega

structure Base (g k : ℕ) (f : Fin 2 → ℕ → ℕ) : Prop where
  matched : ∀ i, Partners (support g k i.val) (f i)
  unique : ∀ i, UniqueLengths (vertexCount g) (support g k i.val) (f i)
  separated : ∀ x∈support g k 0, ∀ y∈support g k 1,
    distance (vertexCount g) x (f 0 x) ≠ distance (vertexCount g) y (f 1 y)

def avoidsBase (g k : ℕ) (f : Fin 2 → ℕ → ℕ) (i : Fin 2) (h : ℕ → ℕ) : Prop :=
  ∀ x∈support g k i.val, ∀ j : Fin 2, ∀ y∈support g k j.val,
    distance (vertexCount g) x (h x) ≠ distance (vertexCount g) y (f j y)

/-- Bit a records the presence of the cyclic edge length a. -/
def lengthMask : List ℕ → ℕ
  | [] => 0
  | a::as => 2^a ||| lengthMask as

theorem lengthMask_mem (A : List ℕ) (a : ℕ) : (lengthMask A).testBit a=true ↔ a∈A := by
  induction A with
  | nil => simp [lengthMask]
  | cons x xs ih =>
    simp only [lengthMask,Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true_iff,decide_eq_true_eq,
      ih,List.mem_cons]
    tauto

def profiles (g k ε : ℕ) : List ℕ :=
  (((lengthProfiles (vertexCount g) g (support g k ε)).filter (fun A => decide A.Nodup)).map lengthMask).eraseDups

def lengthSets (g k : ℕ) : List ℕ :=
  let B := profiles g k 1
  ((profiles g k 0).flatMap fun A =>
    (B.filter (fun b => decide ((A &&& b)=0))).map (fun b => A ||| b)).eraseDups

theorem profiles_complete {g k : ℕ} (hk : k≤2*g) {f : Fin 2 → ℕ → ℕ} (base : Base g k f) (i : Fin 2) :
    ∃ A∈profiles g k i.val, ∀ a, A.testBit a=true → ∃ x∈support g k i.val, a=distance (vertexCount g) x (f i x) := by
  obtain ⟨L,hL,hnd,hs⟩ := lengthProfiles_complete (support_size hk i.val)
    (support_nodup (by have := i.isLt; omega)) (base.matched i) (base.unique i)
  refine ⟨lengthMask L,List.mem_eraseDups.mpr (List.mem_map.mpr ⟨L,
    List.mem_filter.mpr ⟨hL,decide_eq_true hnd⟩,rfl⟩),?_⟩
  exact fun a ha => hs a ((lengthMask_mem L a).mp ha)

theorem lengthSets_complete {g k : ℕ} (hk : k≤2*g) {f : Fin 2 → ℕ → ℕ} (base : Base g k f) :
    ∃ S∈lengthSets g k, ∀ a, S.testBit a=true → ∃ (i : Fin 2), ∃ x∈support g k i.val,
      a=distance (vertexCount g) x (f i x) := by
  obtain ⟨A,hA,hAs⟩ := profiles_complete hk base 0
  obtain ⟨B,hB,hBs⟩ := profiles_complete hk base 1
  have dis : (A &&& B)=0 := by
    apply Nat.eq_of_testBit_eq
    intro a
    simp only [Nat.testBit_and,Nat.zero_testBit]
    cases ha : A.testBit a <;> cases hb : B.testBit a <;> try rfl
    obtain ⟨x,hx,he⟩ := hAs a ha
    obtain ⟨y,hy,hf⟩ := hBs a hb
    exact False.elim (base.separated x hx y hy (he.symm.trans hf))
  refine ⟨A ||| B,List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨A,hA,
    List.mem_map.mpr ⟨B,List.mem_filter.mpr ⟨hB,decide_eq_true dis⟩,rfl⟩⟩),?_⟩
  intro a ha
  rw [Nat.testBit_or,Bool.or_eq_true_iff] at ha
  rcases ha with h|h
  · exact ⟨0,hAs a h⟩
  · exact ⟨1,hBs a h⟩

/-- Discard a forbidden first edge before enumerating the remaining matching. -/
def allowedMatchings (ok : (ℕ × ℕ) → Bool) : ℕ → List ℕ → List (List (ℕ × ℕ))
  | 0, [] => [[]]
  | 0, _::_ => []
  | _+1, [] => []
  | t+1, x::xs => xs.flatMap fun y =>
      if ok (edge x y) then (allowedMatchings ok t (xs.erase y)).map (List.cons (edge x y))
      else []

theorem allowedMatchings_eq (ok : (ℕ × ℕ) → Bool) (t : ℕ) (W : List ℕ) :
    allowedMatchings ok t W=(matchings t W).filter (fun M => M.all ok) := by
  induction t generalizing W with
  | zero => cases W <;> rfl
  | succ t ih =>
    cases W with
    | nil => rfl
    | cons x xs =>
      simp only [allowedMatchings,matchings,List.filter_flatMap]
      congr 1
      funext y
      rw [List.filter_map]
      cases h : ok (edge x y) <;> simp [h,Function.comp_def,ih]

def complements (g k ε S : ℕ) : List (List (ℕ × ℕ)) :=
  allowedMatchings (fun e => decide (S.testBit (distance (vertexCount g) e.1 e.2)≠true))
    g (support g k ε)

def viablePairs (g k : ℕ) : List (List (ℕ × ℕ) × List (ℕ × ℕ)) :=
  ((lengthSets g k).flatMap fun S =>
    let right := complements g k 1 S
    (complements g k 0 S).flatMap fun left => right.map fun r => (left,r)).eraseDups

private theorem edge_length (n x y : ℕ) : distance n (edge x y).1 (edge x y).2=distance n x y := by
  rcases le_total x y with h|h
  · simp [edge,min_eq_left h,max_eq_right h]
  · simpa only [edge,min_eq_right h,max_eq_left h] using distance_swap n y x

theorem complements_complete {g k : ℕ} (hk : k≤2*g) {f : Fin 2 → ℕ → ℕ} (i : Fin 2)
    {h : ℕ → ℕ} (hp : Partners (support g k i.val) h) (avoid : avoidsBase g k f i h)
    {S : ℕ} (hs : ∀ a, S.testBit a=true → ∃ j : Fin 2, ∃ y∈support g k j.val, a=distance (vertexCount g) y (f j y)) :
    ∃ M∈complements g k i.val S, represents M (support g k i.val) h := by
  obtain ⟨M,hm,desc⟩ := matchings_complete (support_size hk _) (support_nodup (by have := i.isLt; omega)) hp
  refine ⟨M,?_,desc⟩
  rw [complements,allowedMatchings_eq]
  refine List.mem_filter.mpr ⟨hm,List.all_eq_true.mpr ?_⟩
  intro e he
  apply decide_eq_true
  intro mem
  obtain ⟨x,hx,rfl⟩ := (desc e).mp he
  rw [edge_length] at mem
  obtain ⟨j,y,hy,eq⟩ := hs _ mem
  exact avoid x hx j y hy eq

theorem viablePairs_complete {g k : ℕ} (hk : k≤2*g) {f : Fin 2 → ℕ → ℕ} (base : Base g k f)
    {h₀ h₁ : ℕ → ℕ} (p₀ : Partners (support g k 0) h₀) (a₀ : avoidsBase g k f 0 h₀)
    (p₁ : Partners (support g k 1) h₁) (a₁ : avoidsBase g k f 1 h₁) :
    ∃ M∈viablePairs g k, represents M.1 (support g k 0) h₀ ∧ represents M.2 (support g k 1) h₁ := by
  obtain ⟨S,hs,source⟩ := lengthSets_complete hk base
  obtain ⟨U,hu,desc⟩ := complements_complete hk 0 p₀ a₀ source
  obtain ⟨V,hv,desc'⟩ := complements_complete hk 1 p₁ a₁ source
  exact ⟨(U,V),List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨S,hs,
    List.mem_flatMap.mpr ⟨U,hu,List.mem_map.mpr ⟨V,hv,rfl⟩⟩⟩),desc,desc'⟩

end CircularIndex.Insertion.Small
