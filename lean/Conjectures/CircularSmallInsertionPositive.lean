import Conjectures.CircularSmallInsertionFixtures

/-! Explicit perfect matchings witnessing feasibility for every forward
insertion colour at k=2 and k=8 on 31 vertices. -/

namespace CircularIndex.Insertion.Small

def partner : List (ℕ × ℕ) → ℕ → ℕ
  | [], x => x
  | (u,v)::es,x => if x=u then v else if x=v then u else partner es x

private def baseTwo (i : Fin 2) : ℕ → ℕ :=
  partner (if i=0 then [(0,18),(1,15),(13,20),(14,19),(16,17)] else
    [(1,17),(2,13),(14,20),(15,19),(16,18)])

private def baseEight (i : Fin 2) : ℕ → ℕ :=
  partner (if i=0 then [(0,7),(1,6),(2,20),(3,4),(5,19)] else
    [(1,7),(2,6),(3,5),(4,20),(8,19)])

private theorem base_two_valid : Base 5 2 baseTwo := by
  constructor
  · unfold Partners; decide
  · unfold UniqueLengths; decide
  · decide

private theorem base_eight_valid : Base 5 8 baseEight := by
  constructor
  · unfold Partners; decide
  · unfold UniqueLengths; decide
  · decide

private theorem two_complements : ∀ i : Fin 2,
    let m := partner (if i=0 then forcedTwo.1 else forcedTwo.2)
    Partners (support 5 2 i.val) m ∧ avoidsBase 5 2 baseTwo i m := by
  unfold Partners avoidsBase
  decide

private theorem eight_complements : ∀ i : Fin 2,
    let m := partner (if i=0 then forcedEight.1 else forcedEight.2)
    Partners (support 5 8 i.val) m ∧ avoidsBase 5 8 baseEight i m := by
  unfold Partners avoidsBase
  decide

private def pushPartner (g c : ℕ) (m : ℕ → ℕ) (x : ℕ) :=
  turn (vertexCount g) (shift g c) (m (unturn (vertexCount g) (shift g c) x))

private theorem push_match {g k : ℕ} (hk : k≤2*g) {f : Fin 2 → ℕ → ℕ} (c : ℕ) {m : ℕ → ℕ}
    (p : Partners (support g k (parity c).val) m) (ad : avoidsBase g k f (parity c) m) :
    admissibleClass g k f c (pushPartner g c m) := by
  let n := vertexCount g
  let t := shift g c
  let W := support g k (parity c).val
  have ht : t<n := shift_lt g c
  have bound (x : ℕ) (hx : x∈W) : x<n := support_lt hk (by have := (parity c).isLt; omega) hx
  have act (x : ℕ) (hx : x∈W) : pushPartner g c m (turn n t x)=turn n t (m x) := by
    change turn n t (m (unturn n t (turn n t x)))=_
    rw [unturn_turn ht (bound x hx)]
  constructor
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    obtain ⟨hm,hi,hd⟩ := p x hx
    rw [act x hx]
    refine ⟨List.mem_map.mpr ⟨m x,hm,rfl⟩,?_,?_⟩
    · rw [act _ hm,hi]
    · intro eq
      have h := congrArg (unturn n t) eq
      rw [unturn_turn ht (bound _ hm),unturn_turn ht (bound x hx)] at h
      exact hd h
  · intro y hy i z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    rw [act x hx,distance_turn ht (bound x hx) (bound _ (p x hx).1)]
    exact ad x hx i z hz

theorem forward_two (c : ℕ) : OneForward 5 2 c := by
  refine ⟨baseTwo,base_two_valid,fun j =>
    let d := colour 5 c j.val
    pushPartner 5 d (partner (if parity d=0 then forcedTwo.1 else forcedTwo.2)),?_⟩
  intro j
  exact push_match (by decide) _ (two_complements _).1 (two_complements _).2

theorem forward_eight (c : ℕ) : OneForward 5 8 c := by
  refine ⟨baseEight,base_eight_valid,fun j =>
    let d := colour 5 c j.val
    pushPartner 5 d (partner (if parity d=0 then forcedEight.1 else forcedEight.2)),?_⟩
  intro j
  exact push_match (by decide) _ (eight_complements _).1 (eight_complements _).2

end CircularIndex.Insertion.Small
