import Conjectures.LiTriplesBridge

/-!
# Connected partitions of type `(3, 2^14)` in `Li.T`: the final count

This file completes the bridge between genuine connected partitions of `Li.T`
of type `(3, 2^{14})` and the eight "good triples" of
`Conjectures/LiTriples2.lean`.

The mathematical content is:

* a perfect matching of a subset of a tree is unique (proved by removing the
  vertex of maximal distance from the root `0`, whose partner is forced);
* an exhaustive, kernel-reducible matching search, with soundness and
  completeness;
* the resulting bijection between connected partitions of type `(3, 2^{14})`
  and the eight good triples;
* the final count `Fintype.card {P // Partition325 P} = 8`.
-/

open SimpleGraph

namespace Li
namespace LiFinal325

instance instDecRel : DecidableRel Li.T.Adj := LiTriples2.instDecRel

/-! ## Matchings as sets of two-element blocks -/

/-- A two-element vertex set that is an edge of `Li.T`. -/
def IsBlock2 (B : Finset (Fin 31)) : Prop :=
  B.card = 2 ∧ ∃ u v, B = {u, v} ∧ Li.T.Adj u v

/-- `M` is a perfect matching of `H` inside `Li.T`: its members are two-element
edges, they are pairwise disjoint and their union is `H`. -/
def IsMatchingOf (M : Finset (Finset (Fin 31))) (H : Finset (Fin 31)) : Prop :=
  (∀ B ∈ M, IsBlock2 B) ∧
  (∀ B ∈ M, B ⊆ H) ∧
  (∀ B ∈ M, ∀ C ∈ M, B ≠ C → Disjoint B C) ∧
  M.biUnion id = H

/-- Every block of a two-element block containing `v` gives a partner of `v`. -/
theorem IsBlock2.exists_partner {B : Finset (Fin 31)} (hB : IsBlock2 B) {v : Fin 31}
    (hv : v ∈ B) : ∃ w, B = {v, w} ∧ Li.T.Adj v w := by
  obtain ⟨-, u, w, rfl, hadj⟩ := hB
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h | h
  · subst h
    exact ⟨w, rfl, hadj⟩
  · subst h
    exact ⟨u, Finset.pair_comm u v, hadj.symm⟩

/-- Erasing a block of a perfect matching leaves a perfect matching of the
complementary vertex set. -/
theorem IsMatchingOf.erase {H : Finset (Fin 31)} {M : Finset (Finset (Fin 31))}
    (hM : IsMatchingOf M H) {B : Finset (Fin 31)} (hB : B ∈ M) :
    IsMatchingOf (M.erase B) (H \ B) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C hC; exact hM.1 C (Finset.mem_of_mem_erase hC)
  · intro C hC x hx
    have hC' : C ∈ M := Finset.mem_of_mem_erase hC
    have hCH : C ⊆ H := hM.2.1 C hC'
    have hCB : C ≠ B := fun h => Finset.notMem_erase B M (h ▸ hC)
    have hdisj : Disjoint C B := hM.2.2.1 C hC' B hB hCB
    exact Finset.mem_sdiff.mpr ⟨hCH hx, fun hxB => Finset.disjoint_left.mp hdisj hx hxB⟩
  · intro C hC D hD hne
    exact hM.2.2.1 C (Finset.mem_of_mem_erase hC) D (Finset.mem_of_mem_erase hD) hne
  · have hins : insert B (M.erase B) = M := Finset.insert_erase hB
    have hU : B ∪ (M.erase B).biUnion id = H := by
      have hins' : (insert B (M.erase B)).biUnion id = B ∪ (M.erase B).biUnion id := by
        rw [Finset.biUnion_insert]
        simp
      rw [← hins', hins]
      exact hM.2.2.2
    ext x
    constructor
    · intro hx
      obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
      have hC' : C ∈ M := Finset.mem_of_mem_erase hC
      have hCB : C ≠ B := fun h => Finset.notMem_erase B M (h ▸ hC)
      have hdisj : Disjoint C B := hM.2.2.1 C hC' B hB hCB
      exact Finset.mem_sdiff.mpr ⟨hM.2.1 C hC' hxC,
        fun hxB => Finset.disjoint_left.mp hdisj hxC hxB⟩
    · intro hx
      have hx' := Finset.mem_sdiff.mp hx
      have hxU : x ∈ B ∪ (M.erase B).biUnion id := by rw [hU]; exact hx'.1
      rcases Finset.mem_union.mp hxU with h | h
      · exact absurd h hx'.2
      · exact h

/-! ## Uniqueness of perfect matchings in a tree -/

/-- A vertex of maximal rank in a nonempty set has at most one neighbour in the set. -/
theorem exists_unique_nbhd {H : Finset (Fin 31)} (hH : H.Nonempty) :
    ∃ v ∈ H, ∀ w₁ ∈ H, ∀ w₂ ∈ H, Li.T.Adj v w₁ → Li.T.Adj v w₂ → w₁ = w₂ := by
  obtain ⟨v, hvH, hvmax⟩ := Finset.exists_max_image H rankOf hH
  refine ⟨v, hvH, ?_⟩
  intro w₁ h₁ w₂ h₂ ha₁ ha₂
  have hr₁ := rank_change v w₁ ha₁
  have hr₂ := rank_change v w₂ ha₂
  have hm₁ := hvmax w₁ h₁
  have hm₂ := hvmax w₂ h₂
  have hl₁ : rankOf w₁ + 1 = rankOf v := by
    rcases hr₁ with h | h
    · omega
    · exact h
  have hl₂ : rankOf w₂ + 1 = rankOf v := by
    rcases hr₂ with h | h
    · omega
    · exact h
  by_contra hne
  exact unique_lower_neighbor v ⟨w₁, w₂, hne, ha₁.symm, ha₂.symm, hl₁, hl₂⟩

/-- A perfect matching of a subset of a tree is unique. -/
theorem IsMatchingOf.unique {H : Finset (Fin 31)} :
    ∀ {M M' : Finset (Finset (Fin 31))}, IsMatchingOf M H → IsMatchingOf M' H → M = M' := by
  classical
  induction H using Finset.strongInductionOn with
  | _ H ih =>
    intro M M' hM hM'
    by_cases hH : H.Nonempty
    · obtain ⟨v, hvH, hvuniq⟩ := exists_unique_nbhd hH
      have hvM : v ∈ M.biUnion id := by rw [hM.2.2.2]; exact hvH
      have hvM' : v ∈ M'.biUnion id := by rw [hM'.2.2.2]; exact hvH
      obtain ⟨B, hBM, hvB⟩ := Finset.mem_biUnion.mp hvM
      obtain ⟨B', hB'M, hvB'⟩ := Finset.mem_biUnion.mp hvM'
      obtain ⟨w, hBw, hvw⟩ := (hM.1 B hBM).exists_partner hvB
      obtain ⟨w', hB'w', hvw'⟩ := (hM'.1 B' hB'M).exists_partner hvB'
      have hwH : w ∈ H := hM.2.1 B hBM (by rw [hBw]; simp)
      have hw'H : w' ∈ H := hM'.2.1 B' hB'M (by rw [hB'w']; simp)
      have hww' : w = w' := hvuniq w hwH w' hw'H hvw hvw'
      have hBB' : B = B' := by rw [hBw, hB'w', hww']
      have hBsub : B ⊆ H := hM.2.1 B hBM
      have hcardB : B.card = 2 := (hM.1 B hBM).1
      have hcardH : 2 ≤ H.card := hcardB ▸ Finset.card_le_card hBsub
      have hlt : (H \ B).card < H.card := by
        rw [Finset.card_sdiff]
        have hinter : B ∩ H = B := Finset.inter_eq_left.mpr hBsub
        rw [hinter, hcardB]
        omega
      have hssub : (H \ B) ⊂ H := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
        intro heq
        rw [heq] at hlt
        exact Nat.lt_irrefl _ hlt
      have hErase : IsMatchingOf (M.erase B) (H \ B) := hM.erase hBM
      have hErase' : IsMatchingOf (M'.erase B) (H \ B) := by
        rw [hBB']
        exact hM'.erase hB'M
      have huniq := ih (H \ B) hssub hErase hErase'
      have h1 : insert B (M.erase B) = M := Finset.insert_erase hBM
      have h2 : insert B (M'.erase B) = M' := by
        rw [hBB']
        exact Finset.insert_erase hB'M
      calc M = insert B (M.erase B) := h1.symm
        _ = insert B (M'.erase B) := by rw [huniq]
        _ = M' := h2
    · have hH0 : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
      have hMe : M = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro B hB
        have hBsub : B ⊆ H := hM.2.1 B hB
        have hB2 : B.card = 2 := (hM.1 B hB).1
        have hB0 : B = ∅ := by
          rw [hH0] at hBsub
          exact Finset.subset_empty.mp hBsub
        rw [hB0] at hB2
        exact absurd hB2 (by simp)
      have hMe' : M' = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro B hB
        have hBsub : B ⊆ H := hM'.2.1 B hB
        have hB2 : B.card = 2 := (hM'.1 B hB).1
        have hB0 : B = ∅ := by
          rw [hH0] at hBsub
          exact Finset.subset_empty.mp hBsub
        rw [hB0] at hB2
        exact absurd hB2 (by simp)
      rw [hMe, hMe']

/-! ## An exhaustive, kernel-reducible matching search -/

/-- The neighbours of `v` inside `H`, as a list. -/
def nbrList (H : Finset (Fin 31)) (v : Fin 31) : List (Fin 31) :=
  (List.finRange 31).filter (fun w => decide (Li.T.Adj v w) && decide (w ∈ H))

theorem mem_nbrList {H : Finset (Fin 31)} {v w : Fin 31} :
    w ∈ nbrList H v ↔ Li.T.Adj v w ∧ w ∈ H := by
  simp [nbrList, Bool.and_eq_true]

/-- Exhaustive perfect-matching search, processing vertices in list order. -/
def matchSearch : List (Fin 31) → Finset (Fin 31) → Bool
  | [], H => decide (H = ∅)
  | v :: vs, H =>
      if v ∈ H then (nbrList H v).any (fun w => matchSearch vs (H.erase v |>.erase w))
      else matchSearch vs H

/-- `hasPM H` is `true` iff `H` has a perfect matching inside `Li.T`. -/
def hasPM (H : Finset (Fin 31)) : Bool := matchSearch (List.finRange 31) H

theorem union_sdiff_pair {H : Finset (Fin 31)} {u v : Fin 31} (hu : u ∈ H) (hv : v ∈ H) :
    ({u, v} : Finset (Fin 31)) ∪ (H \ {u, v}) = H := by
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨h, -⟩)
    · rcases h with rfl | rfl <;> assumption
    · exact h
  · intro hx
    by_cases h : x = u
    · exact Or.inl (Or.inl h)
    · by_cases h' : x = v
      · exact Or.inl (Or.inr h')
      · exact Or.inr ⟨hx, by simp [h, h']⟩

/-- Inserting a new two-element block into a matching of the complementary set
gives a matching of the whole set. -/
theorem IsMatchingOf.insert {H : Finset (Fin 31)} {M : Finset (Finset (Fin 31))}
    {u v : Fin 31} (hu : u ∈ H) (hv : v ∈ H) (huv : Li.T.Adj u v)
    (hM : IsMatchingOf M (H \ {u, v})) :
    IsMatchingOf (insert {u, v} M) H := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_insert.mp hB with hBuv | hBM
    · rw [hBuv]
      exact ⟨by simp [huv.1], u, v, rfl, huv⟩
    · exact hM.1 B hBM
  · intro B hB x hx
    rcases Finset.mem_insert.mp hB with hBuv | hBM
    · rw [hBuv] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hu
      · exact hv
    · exact Finset.mem_sdiff.mp (hM.2.1 B hBM hx) |>.1
  · intro B hB C hC hne
    rcases Finset.mem_insert.mp hB with hBuv | hBM
    · rcases Finset.mem_insert.mp hC with hCuv | hCM
      · exact absurd (hBuv.trans hCuv.symm) hne
      · rw [hBuv, Finset.disjoint_left]
        intro x hx hxC
        exact (Finset.mem_sdiff.mp (hM.2.1 C hCM hxC)).2 hx
    · rcases Finset.mem_insert.mp hC with hCuv | hCM
      · rw [hCuv, Finset.disjoint_left]
        intro x hxB hx
        exact (Finset.mem_sdiff.mp (hM.2.1 B hBM hxB)).2 hx
      · exact hM.2.2.1 B hBM C hCM hne
  · rw [Finset.biUnion_insert]
    simp only [id]
    rw [hM.2.2.2, union_sdiff_pair hu hv]

theorem matchSearch_sound : ∀ (vs : List (Fin 31)) (H : Finset (Fin 31)),
    matchSearch vs H = true → ∃ M, IsMatchingOf M H := by
  intro vs
  induction vs with
  | nil =>
    intro H h
    have hH : H = ∅ := of_decide_eq_true h
    subst hH
    exact ⟨∅, by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp⟩
  | cons v vs ih =>
    intro H h
    by_cases hv : v ∈ H
    · rw [matchSearch, ite_eq_left hv] at h
      obtain ⟨w, hw, hwsearch⟩ := List.any_eq_true.mp h
      obtain ⟨M, hM⟩ := ih (H.erase v |>.erase w) hwsearch
      have hadj : Li.T.Adj v w := (mem_nbrList.mp hw).1
      have hwH : w ∈ H := (mem_nbrList.mp hw).2
      have hEq : (H.erase v).erase w = H \ {v, w} := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hEq] at hM
      exact ⟨insert {v, w} M, hM.insert hv hwH hadj⟩
    · rw [matchSearch, ite_eq_right hv] at h
      exact ih H h

theorem matchSearch_complete : ∀ (vs : List (Fin 31)) (H : Finset (Fin 31)),
    (∀ x ∈ H, x ∈ vs) → (∃ M, IsMatchingOf M H) → matchSearch vs H = true := by
  intro vs
  induction vs with
  | nil =>
    intro H hcover h
    obtain ⟨M, hM⟩ := h
    have hH : H = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      exact List.not_mem_nil (hcover x hx)
    subst hH
    simp [matchSearch]
  | cons v vs ih =>
    intro H hcover h
    obtain ⟨M, hM⟩ := h
    by_cases hv : v ∈ H
    · rw [matchSearch, ite_eq_left hv]
      have hvM : v ∈ M.biUnion id := by rw [hM.2.2.2]; exact hv
      obtain ⟨B, hBM, hvB⟩ := Finset.mem_biUnion.mp hvM
      obtain ⟨w, hBw, hvw⟩ := (hM.1 B hBM).exists_partner hvB
      have hwH : w ∈ H := hM.2.1 B hBM (by rw [hBw]; simp)
      have hEq : (H.erase v).erase w = H \ B := by
        rw [hBw]
        ext x
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have hsub : ∀ x ∈ H \ B, x ∈ vs := by
        intro x hx
        have hxH := (Finset.mem_sdiff.mp hx).1
        rcases List.mem_cons.mp (hcover x hxH) with h | h
        · subst h
          exact absurd ((Finset.mem_sdiff.mp hx).2) (by rw [hBw]; simp)
        · exact h
      have hM' : IsMatchingOf (M.erase B) (H \ B) := hM.erase hBM
      have hsearch : matchSearch vs ((H.erase v).erase w) = true := by
        rw [hEq]
        exact ih (H \ B) hsub ⟨M.erase B, hM'⟩
      exact List.any_eq_true.mpr ⟨w, mem_nbrList.mpr ⟨hvw, hwH⟩, hsearch⟩
    · have hcover' : ∀ x ∈ H, x ∈ vs := by
        intro x hx
        rcases List.mem_cons.mp (hcover x hx) with h | h
        · subst h
          exact absurd hx hv
        · exact h
      rw [matchSearch, ite_eq_right hv]
      exact ih H hcover' ⟨M, hM⟩

theorem hasPM_iff (H : Finset (Fin 31)) :
    hasPM H = true ↔ ∃ M, IsMatchingOf M H := by
  constructor
  · exact matchSearch_sound (List.finRange 31) H
  · intro h
    exact matchSearch_complete (List.finRange 31) H (fun x _ => List.mem_finRange x) h

/-! ## The eight good triples and the finite classification -/

/-- The eight connected triples whose complement has a perfect matching. -/
def goodTripleSets : Finset (Finset (Fin 31)) :=
  [ ({0, 1, 16} : Finset (Fin 31)), {16, 17, 18}, {18, 19, 20}, {20, 21, 22},
    {22, 23, 24}, {24, 25, 26}, {26, 27, 28}, {28, 29, 30} ].toFinset

theorem goodTripleSets_card : goodTripleSets.card = 8 := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem goodTripleSets_hasPM :
    ∀ S ∈ goodTripleSets, hasPM (Finset.univ \ S) = true := by
  intro S hS
  simp only [goodTripleSets, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
/-- The same classification with the adjacency tests first. The decision then
visits only the 60 oriented edges before choosing `c`, which keeps the kernel within
the CI memory cap. -/
theorem path_triple_classify_adj :
    ∀ a b : Fin 31, Li.T.Adj a b → ∀ c : Fin 31, Li.T.Adj b c → a ≠ c →
      hasPM (Finset.univ \ ({a, b, c} : Finset (Fin 31))) = true →
      ({a, b, c} : Finset (Fin 31)) ∈ goodTripleSets := by
  decide

theorem path_triple_classify :
    ∀ a b c : Fin 31, a ≠ b → b ≠ c → a ≠ c → Li.T.Adj a b → Li.T.Adj b c →
      hasPM (Finset.univ \ ({a, b, c} : Finset (Fin 31))) = true →
      ({a, b, c} : Finset (Fin 31)) ∈ goodTripleSets :=
  fun a b c _ _ hac hab hbc hpm => path_triple_classify_adj a b hab c hbc hac hpm

/-! ## Walks staying inside a vertex set -/

theorem walkIn_nil {S : Finset (Fin 31)} {u : Fin 31} (hu : u ∈ S) :
    LiBridge.WalkIn S (SimpleGraph.Walk.nil (G := Li.T) (u := u)) := by
  intro x hx
  rw [SimpleGraph.Walk.support_nil] at hx
  rw [List.mem_singleton.mp hx]
  exact hu

theorem walkIn_pair {S : Finset (Fin 31)} {u v : Fin 31} (hu : u ∈ S) (hv : v ∈ S)
    (h : Li.T.Adj u v) :
    LiBridge.WalkIn S (SimpleGraph.Walk.cons h (SimpleGraph.Walk.nil (G := Li.T) (u := v))) := by
  intro x hx
  rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact hu
  · rw [List.mem_singleton.mp hx']
    exact hv

theorem walkIn_triple {S : Finset (Fin 31)} {a b c : Fin 31} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (h1 : Li.T.Adj a b) (h2 : Li.T.Adj b c) :
    LiBridge.WalkIn S (SimpleGraph.Walk.cons h1
      (SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.nil (G := Li.T) (u := c)))) := by
  intro x hx
  rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_nil] at hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact ha
  rcases List.mem_cons.mp hx' with rfl | hx''
  · exact hb
  · rw [List.mem_singleton.mp hx'']
    exact hc

theorem walkIn_pair_flip {S : Finset (Fin 31)} {u v : Fin 31} (hu : u ∈ S) (hv : v ∈ S)
    (h : Li.T.Adj u v) :
    LiBridge.WalkIn S (SimpleGraph.Walk.cons h.symm (SimpleGraph.Walk.nil (G := Li.T) (u := u))) := by
  intro z hz
  rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hz
  rcases List.mem_cons.mp hz with rfl | hz'
  · exact hv
  · rw [List.mem_singleton.mp hz']
    exact hu

/-- A two-element edge spans a connected subgraph. -/
theorem connIn_pair {u v : Fin 31} (h : Li.T.Adj u v) :
    LiBridge.ConnIn ({u, v} : Finset (Fin 31)) := by
  constructor
  · exact ⟨u, Finset.mem_insert_self u {v}⟩
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl
      · exact ⟨SimpleGraph.Walk.nil, walkIn_nil (by simp)⟩
      · exact ⟨SimpleGraph.Walk.cons h SimpleGraph.Walk.nil,
          walkIn_pair (by simp) (by simp) h⟩
    · rcases hy with rfl | rfl
      · exact ⟨SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil,
          walkIn_pair_flip (by simp) (by simp) h⟩
      · exact ⟨SimpleGraph.Walk.nil, walkIn_nil (by simp)⟩

/-- A path of two edges spans a connected subgraph. -/
theorem connIn_of_path {a b c : Fin 31} (hab : a ≠ b) (hbc : b ≠ c) (_hac : a ≠ c)
    (h1 : Li.T.Adj a b) (h2 : Li.T.Adj b c) :
    LiBridge.ConnIn ({a, b, c} : Finset (Fin 31)) := by
  constructor
  · exact ⟨a, by simp⟩
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact ⟨SimpleGraph.Walk.nil, walkIn_nil (by simp)⟩
    · exact ⟨SimpleGraph.Walk.cons h1 SimpleGraph.Walk.nil,
        walkIn_pair (by simp) (by simp) h1⟩
    · exact ⟨SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil),
        walkIn_triple (by simp) (by simp) (by simp) h1 h2⟩
    · exact ⟨SimpleGraph.Walk.cons h1.symm SimpleGraph.Walk.nil,
        walkIn_pair (by simp) (by simp) h1.symm⟩
    · exact ⟨SimpleGraph.Walk.nil, walkIn_nil (by simp)⟩
    · exact ⟨SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil,
        walkIn_pair (by simp) (by simp) h2⟩
    · exact ⟨SimpleGraph.Walk.cons h2.symm (SimpleGraph.Walk.cons h1.symm SimpleGraph.Walk.nil),
        walkIn_triple (by simp) (by simp) (by simp) h2.symm h1.symm⟩
    · exact ⟨SimpleGraph.Walk.cons h2.symm SimpleGraph.Walk.nil,
        walkIn_pair (by simp) (by simp) h2.symm⟩
    · exact ⟨SimpleGraph.Walk.nil, walkIn_nil (by simp)⟩

/-! ## The three-block of a `(3, 2^14)`-partition -/

/-- The union of the size-three blocks (a single block under `Partition325`). -/
noncomputable def threeBlock (P : Finset (Finset (Fin 31))) : Finset (Fin 31) :=
  (P.filter (fun B => B.card = 3)).sup id

theorem threeBlock_eq_of_filter {P : Finset (Finset (Fin 31))} {B : Finset (Fin 31)}
    (h : P.filter (fun B => B.card = 3) = {B}) : threeBlock P = B := by
  unfold threeBlock
  rw [h, Finset.sup_singleton]
  rfl

theorem exists_threeBlock {P : Finset (Finset (Fin 31))} (hP : LiBridge.Partition325 P) :
    ∃ B, P.filter (fun B => B.card = 3) = {B} :=
  Finset.card_eq_one.mp hP.2.1.1

theorem threeBlock_mem {P : Finset (Finset (Fin 31))} (hP : LiBridge.Partition325 P) :
    threeBlock P ∈ P := by
  obtain ⟨B, hB⟩ := exists_threeBlock hP
  have hBmem : B ∈ P.filter (fun B => B.card = 3) := by
    rw [hB]; exact Finset.mem_singleton_self B
  rw [threeBlock_eq_of_filter hB]
  exact (Finset.mem_filter.mp hBmem).1

theorem threeBlock_card {P : Finset (Finset (Fin 31))} (hP : LiBridge.Partition325 P) :
    (threeBlock P).card = 3 := by
  obtain ⟨B, hB⟩ := exists_threeBlock hP
  have hBmem : B ∈ P.filter (fun B => B.card = 3) := by
    rw [hB]; exact Finset.mem_singleton_self B
  rw [threeBlock_eq_of_filter hB]
  exact (Finset.mem_filter.mp hBmem).2

theorem eq_threeBlock_of_partition {P : Finset (Finset (Fin 31))} (hP : LiBridge.Partition325 P)
    {C : Finset (Fin 31)} (hC : C ∈ P) (hcard : C.card = 3) : C = threeBlock P := by
  obtain ⟨B, hB⟩ := exists_threeBlock hP
  have hCmem : C ∈ P.filter (fun B => B.card = 3) := Finset.mem_filter.mpr ⟨hC, hcard⟩
  rw [hB] at hCmem
  have hCB : C = B := by simpa using hCmem
  rw [hCB, threeBlock_eq_of_filter hB]

theorem threeBlock_conn {P : Finset (Finset (Fin 31))} (hP : LiBridge.Partition325 P) :
    LiBridge.ConnIn (threeBlock P) :=
  hP.2.2 (threeBlock P) (threeBlock_mem hP)

/-- The size-two blocks of a `(3, 2^14)`-partition form a perfect matching of the
complement of the three-block. -/
theorem isMatchingOf_erase_threeBlock {P : Finset (Finset (Fin 31))}
    (hP : LiBridge.Partition325 P) :
    IsMatchingOf (P.erase (threeBlock P)) (Finset.univ \ threeBlock P) := by
  classical
  set S := threeBlock P with hSdef
  have hS : S ∈ P := threeBlock_mem hP
  have hS3 : S.card = 3 := threeBlock_card hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hB
    have hB' : B ∈ P := Finset.mem_of_mem_erase hB
    have hBne : B ≠ S := Finset.ne_of_mem_erase hB
    rcases hP.2.1.2 B hB' with h3 | h2
    · exact absurd (eq_threeBlock_of_partition hP hB' h3) hBne
    · exact ⟨h2, LiBridge.conn2_adj h2 (hP.2.2 B hB')⟩
  · intro B hB x hx
    have hB' : B ∈ P := Finset.mem_of_mem_erase hB
    have hBne : B ≠ S := Finset.ne_of_mem_erase hB
    have hdisj : Disjoint B S := hP.1.2.1 B hB' S hS hBne
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hxS => Finset.disjoint_left.mp hdisj hx hxS⟩
  · intro B hB C hC hne
    exact hP.1.2.1 B (Finset.mem_of_mem_erase hB) C (Finset.mem_of_mem_erase hC) hne
  · have hins : insert S (P.erase S) = P := Finset.insert_erase hS
    have hU : S ∪ (P.erase S).biUnion id = Finset.univ := by
      have hins' : (insert S (P.erase S)).biUnion id = S ∪ (P.erase S).biUnion id := by
        rw [Finset.biUnion_insert]
        simp
      rw [← hins', hins]
      exact hP.1.2.2
    ext x
    constructor
    · intro hx
      obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
      have hC' : C ∈ P := Finset.mem_of_mem_erase hC
      have hCne : C ≠ S := Finset.ne_of_mem_erase hC
      have hdisj : Disjoint C S := hP.1.2.1 C hC' S hS hCne
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        fun hxS => Finset.disjoint_left.mp hdisj hxC hxS⟩
    · intro hx
      have hx' := Finset.mem_sdiff.mp hx
      have hxU : x ∈ S ∪ (P.erase S).biUnion id := by rw [hU]; exact hx'.1
      rcases Finset.mem_union.mp hxU with h | h
      · exact absurd h hx'.2
      · exact h

/-! ## Building a partition from a connected triple and a matching -/

theorem filter_insert_three {S : Finset (Fin 31)} {M : Finset (Finset (Fin 31))}
    (hS3 : S.card = 3) (hM : IsMatchingOf M (Finset.univ \ S)) :
    (insert S M).filter (fun B => B.card = 3) = {S} := by
  classical
  ext B
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hBmem, hBcard⟩
    rcases hBmem with hBS | hBM
    · exact hBS
    · exact absurd hBcard (by have := (hM.1 B hBM).1; omega)
  · rintro rfl
    exact ⟨Or.inl rfl, hS3⟩

theorem threeBlock_insert {S : Finset (Fin 31)} {M : Finset (Finset (Fin 31))}
    (hS3 : S.card = 3) (hM : IsMatchingOf M (Finset.univ \ S)) :
    threeBlock (insert S M) = S :=
  threeBlock_eq_of_filter (filter_insert_three hS3 hM)

/-- A connected triple together with a perfect matching of its complement is a
connected partition of type `(3, 2^14)`. -/
theorem partition_insert_of_matching {S : Finset (Fin 31)} {M : Finset (Finset (Fin 31))}
    (hS3 : S.card = 3) (hSC : LiBridge.ConnIn S)
    (hM : IsMatchingOf M (Finset.univ \ S)) :
    LiBridge.Partition325 (insert S M) := by
  classical
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro B hB
    rcases Finset.mem_insert.mp hB with hBS | hBM
    · rw [hBS]; exact Finset.card_pos.mp (by omega)
    · exact Finset.card_pos.mp (by have := (hM.1 B hBM).1; omega)
  · intro B hB C hC hne
    rcases Finset.mem_insert.mp hB with hBS | hBM
    · rcases Finset.mem_insert.mp hC with hCS | hCM
      · exact absurd (hBS.trans hCS.symm) hne
      · rw [hBS, Finset.disjoint_left]
        intro x hx hxC
        exact (Finset.mem_sdiff.mp (hM.2.1 C hCM hxC)).2 hx
    · rcases Finset.mem_insert.mp hC with hCS | hCM
      · rw [hCS, Finset.disjoint_left]
        intro x hxB hx
        exact (Finset.mem_sdiff.mp (hM.2.1 B hBM hxB)).2 hx
      · exact hM.2.2.1 B hBM C hCM hne
  · rw [Finset.biUnion_insert]
    simp only [id]
    rw [hM.2.2.2]
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with h | h
      · exact Finset.mem_univ x
      · exact (Finset.mem_sdiff.mp h).1
    · intro hx
      by_cases hxS : x ∈ S
      · exact Finset.mem_union.mpr (Or.inl hxS)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxS⟩))
  · rw [filter_insert_three hS3 hM]
    simp
  · intro B hB
    rcases Finset.mem_insert.mp hB with hBS | hBM
    · exact Or.inl (hBS ▸ hS3)
    · exact Or.inr (hM.1 B hBM).1
  · intro B hB
    rcases Finset.mem_insert.mp hB with hBS | hBM
    · rw [hBS]; exact hSC
    · obtain ⟨-, u, v, hBuv, huv⟩ := hM.1 B hBM
      rw [hBuv]
      exact connIn_pair huv

/-! ## The bijection and the count -/

/-- A connected triple whose complement has a perfect matching. -/
def GoodTripleData (S : Finset (Fin 31)) : Prop :=
  S.card = 3 ∧ LiBridge.ConnIn S ∧ ∃ M, IsMatchingOf M (Finset.univ \ S)

/-- Membership in the eight triples gives the connectivity data. -/
theorem goodTripleSets_card3 : ∀ S ∈ goodTripleSets, S.card = 3 := by
  intro S hS
  simp only [goodTripleSets, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem goodTripleSets_connIn : ∀ S ∈ goodTripleSets, LiBridge.ConnIn S := by
  intro S hS
  simp only [goodTripleSets, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := connIn_of_path (a := 1) (b := 0) (c := 16) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    rwa [show ({1, 0, 16} : Finset (Fin 31)) = {0, 1, 16} by decide] at h
  · exact connIn_of_path (a := 16) (b := 17) (c := 18) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · exact connIn_of_path (a := 18) (b := 19) (c := 20) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · exact connIn_of_path (a := 20) (b := 21) (c := 22) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · exact connIn_of_path (a := 22) (b := 23) (c := 24) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · exact connIn_of_path (a := 24) (b := 25) (c := 26) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · exact connIn_of_path (a := 26) (b := 27) (c := 28) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · exact connIn_of_path (a := 28) (b := 29) (c := 30) (by decide) (by decide) (by decide)
      (by decide) (by decide)

/-- The classification: a connected triple whose complement has a perfect matching
is one of the eight listed triples. -/
theorem goodTripleData_iff (S : Finset (Fin 31)) : GoodTripleData S ↔ S ∈ goodTripleSets := by
  constructor
  · rintro ⟨h3, hC, ⟨M, hM⟩⟩
    obtain ⟨a, b, c, hab, hbc, hac, hS, hadj1, hadj2⟩ := LiBridge.conn3_path h3 hC
    have hM' : IsMatchingOf M (Finset.univ \ ({a, b, c} : Finset (Fin 31))) := by
      rw [← hS]
      exact hM
    have hpm : hasPM (Finset.univ \ ({a, b, c} : Finset (Fin 31))) = true :=
      (hasPM_iff _).mpr ⟨M, hM'⟩
    have hclass := path_triple_classify a b c hab hbc hac hadj1 hadj2 hpm
    rwa [← hS] at hclass
  · intro hS
    exact ⟨goodTripleSets_card3 S hS, goodTripleSets_connIn S hS,
      (hasPM_iff _).mp (goodTripleSets_hasPM S hS)⟩

noncomputable def partToGood
    (P : {P : Finset (Finset (Fin 31)) // LiBridge.Partition325 P}) :
    {S : Finset (Fin 31) // GoodTripleData S} :=
  ⟨threeBlock P.1, threeBlock_card P.2, threeBlock_conn P.2,
    ⟨P.1.erase (threeBlock P.1), isMatchingOf_erase_threeBlock P.2⟩⟩

noncomputable def goodToPart (S : {S : Finset (Fin 31) // GoodTripleData S}) :
    {P : Finset (Finset (Fin 31)) // LiBridge.Partition325 P} :=
  ⟨insert S.1 (Classical.choose S.2.2.2),
    partition_insert_of_matching S.2.1 S.2.2.1 (Classical.choose_spec S.2.2.2)⟩

theorem partToGood_goodToPart (S : {S : Finset (Fin 31) // GoodTripleData S}) :
    partToGood (goodToPart S) = S := by
  apply Subtype.ext
  exact threeBlock_insert S.2.1 (Classical.choose_spec S.2.2.2)

theorem goodToPart_partToGood
    (P : {P : Finset (Finset (Fin 31)) // LiBridge.Partition325 P}) :
    goodToPart (partToGood P) = P := by
  apply Subtype.ext
  have hM2 : IsMatchingOf (Classical.choose (partToGood P).2.2.2)
      (Finset.univ \ threeBlock P.1) := Classical.choose_spec (partToGood P).2.2.2
  have hM1 : IsMatchingOf (P.1.erase (threeBlock P.1)) (Finset.univ \ threeBlock P.1) :=
    isMatchingOf_erase_threeBlock P.2
  have huniq : Classical.choose (partToGood P).2.2.2 = P.1.erase (threeBlock P.1) :=
    IsMatchingOf.unique hM2 hM1
  show insert (threeBlock P.1) (Classical.choose (partToGood P).2.2.2) = P.1
  rw [huniq]
  exact Finset.insert_erase (threeBlock_mem P.2)

noncomputable def partEquiv :
    {P : Finset (Finset (Fin 31)) // LiBridge.Partition325 P} ≃
      {S : Finset (Fin 31) // GoodTripleData S} where
  toFun := partToGood
  invFun := goodToPart
  left_inv := goodToPart_partToGood
  right_inv := partToGood_goodToPart

section ClassicalDecidable

attribute [local instance] Classical.propDecidable

theorem card_goodTripleData :
    Fintype.card {S : Finset (Fin 31) // GoodTripleData S} = 8 := by
  classical
  rw [Fintype.card_congr (Equiv.subtypeEquivRight goodTripleData_iff)]
  rw [Fintype.card_coe, goodTripleSets_card]

/-- **The connected-partition count.** `Li.T` has exactly eight connected
partitions into one block of size three and fourteen blocks of size two. -/
theorem b_triple_pairs :
    Fintype.card {P : Finset (Finset (Fin 31)) // LiBridge.Partition325 P} = 8 := by
  classical
  rw [Fintype.card_congr partEquiv, card_goodTripleData]

end ClassicalDecidable

end LiFinal325
end Li
