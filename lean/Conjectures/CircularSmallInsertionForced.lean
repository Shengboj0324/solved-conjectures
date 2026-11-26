import Conjectures.CircularSmallInsertionWindows

/-! When the exhaustive search singles out one pair of complement matchings,
each edge of every allowed insertion block is forced on the labelled graph. -/

namespace CircularIndex.Insertion.Small

abbrev Matching := List (ℕ × ℕ)
abbrev MatchPair := Matching × Matching

def entry (M : MatchPair) (i : Fin 2) := if i=0 then M.1 else M.2

theorem forced_class {g k : ℕ} (hk : k≤2*g) {f : Fin 2 → ℕ → ℕ} (base : Base g k f)
    (supply : ∀ i : Fin 2, ∃ m, Partners (support g k i.val) m ∧ avoidsBase g k f i m)
    {M : MatchPair} (only : viablePairs g k=[M]) (i : Fin 2) {h : ℕ → ℕ}
    (p : Partners (support g k i.val) h) (a : avoidsBase g k f i h) :
    represents (entry M i) (support g k i.val) h := by
  have cases : i=0 ∨ i=1 := by
    have := i.isLt
    rcases (show i.val=0 ∨ i.val=1 by omega) with h|h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases cases with rfl|rfl
  · obtain ⟨h₁,p₁,a₁⟩ := supply 1
    obtain ⟨T,ht,desc,_⟩ := viablePairs_complete hk base p a p₁ a₁
    rw [only,List.mem_singleton] at ht
    exact ht ▸ desc
  · obtain ⟨h₀,p₀,a₀⟩ := supply 0
    obtain ⟨T,ht,_,desc⟩ := viablePairs_complete hk base p₀ a₀ p a
    rw [only,List.mem_singleton] at ht
    simpa [entry] using (ht ▸ desc : represents M.2 _ h)

def turnEdge (g c : ℕ) (e : ℕ × ℕ) :=
  edge (turn (vertexCount g) (shift g c) e.1) (turn (vertexCount g) (shift g c) e.2)

private theorem turn_edge (g c x y : ℕ) : turnEdge g c (edge x y)=
    edge (turn (vertexCount g) (shift g c) x) (turn (vertexCount g) (shift g c) y) := by
  rcases le_total x y with h|h
  · simp only [turnEdge,edge,min_eq_left h,max_eq_right h]
  · rw [edge_swap x y]
    change edge _ _=edge _ _
    rw [show edge y x=(y,x) from by simp [edge,min_eq_left h,max_eq_right h]]
    apply edge_swap

def classEdges (g k c : ℕ) (h : ℕ → ℕ) : Set (ℕ × ℕ) :=
  {e | ∃ x∈classSupport g k c, e=edge x (h x)}

theorem forced_edges {g k c : ℕ} (hk : k≤2*g) {f : Fin 2 → ℕ → ℕ} {h : ℕ → ℕ}
    (ad : admissibleClass g k f c h) {L : Matching}
    (rep : represents L (support g k (parity c).val) (liftPartner g c h)) (e : ℕ × ℕ) :
    e∈L.map (turnEdge g c) ↔ e∈classEdges g k c h := by
  have liftEq := (pullback_partners hk ad.1).2
  constructor
  · intro he
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp he
    obtain ⟨x,hx,rfl⟩ := (rep b).mp hb
    refine ⟨turn (vertexCount g) (shift g c) x,List.mem_map.mpr ⟨x,hx,rfl⟩,?_⟩
    rw [turn_edge,liftEq x hx]
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    refine List.mem_map.mpr ⟨edge x (liftPartner g c h x),(rep _).mpr ⟨x,hx,rfl⟩,?_⟩
    rw [turn_edge,liftEq x hx]

def forcedBlock (g c : ℕ) (M : MatchPair) : Matching :=
  (List.finRange 3).flatMap fun j =>
    let d := colour g c j.val
    (entry M (parity d)).map (turnEdge g d)

def windowEdges (g k c : ℕ) (h : Fin 3 → ℕ → ℕ) : Set (ℕ × ℕ) :=
  {e | ∃ j : Fin 3, e∈classEdges g k (colour g c j.val) (h j)}

theorem forced_window {g k c : ℕ} (hk : k≤2*g) {f : Fin 2 → ℕ → ℕ} (base : Base g k f)
    {M : MatchPair} (only : viablePairs g k=[M]) {h : Fin 3 → ℕ → ℕ}
    (hw : ∀ j, admissibleClass g k f (colour g c j.val) (h j)) (e : ℕ × ℕ) :
    e∈forcedBlock g c M ↔ e∈windowEdges g k c h := by
  have eq (j : Fin 3) :=
    let c' := colour g c j.val
    let ad := admissible_pullback hk (hw j)
    forced_edges hk (hw j) (forced_class hk base (window_supplies hk hw) only
      (parity c') ad.1 ad.2) e
  constructor
  · intro he
    obtain ⟨j,_,hm⟩ := List.mem_flatMap.mp he
    exact ⟨j,(eq j).mp hm⟩
  · rintro ⟨j,hm⟩
    exact List.mem_flatMap.mpr ⟨j,List.mem_finRange j,(eq j).mpr hm⟩

/-- Three arbitrary forward insertion colours and all nine actual matchings.
Distinct blocks must have disjoint sets of unordered labelled edges. -/
def ThreeForward (g k : ℕ) (c : Fin 3 → Fin (2*vertexCount g)) : Prop :=
  ∃ f : Fin 2 → ℕ → ℕ, Base g k f ∧ ∃ h : Fin 3 → Fin 3 → ℕ → ℕ,
    (∀ i j, admissibleClass g k f (colour g (c i).val j.val) (h i j)) ∧
      ∀ i j : Fin 3, i≠j → ∀ e∈windowEdges g k (c i).val (h i), e∉windowEdges g k (c j).val (h j)

end CircularIndex.Insertion.Small
