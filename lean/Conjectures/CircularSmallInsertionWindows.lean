import Conjectures.CircularSmallInsertionSearch

/-! Labelled supports for the forward cyclic insertion problem. Rotating a
perfect matching to or from its base support preserves all of its lengths. -/

namespace CircularIndex.Insertion.Small

def parity (c : ℕ) : Fin 2 := ⟨c%2,Nat.mod_lt _ (by decide)⟩

def colour (g c j : ℕ) := (c+j)%(2*vertexCount g)
def shift (g c : ℕ) := (((4*g+1)*c)%(2*vertexCount g))/2

def turn (n t x : ℕ) := (x+t)%n
def unturn (n t x : ℕ) := (x+n-t)%n

theorem shift_lt (g c : ℕ) : shift g c < vertexCount g := by
  have hn : 0<vertexCount g := by unfold vertexCount; omega
  have := Nat.mod_lt ((4*g+1)*c) (show 0<2*vertexCount g by omega)
  unfold shift
  omega

theorem unturn_turn {n t x : ℕ} (ht : t<n) (hx : x<n) : unturn n t (turn n t x)=x := by
  unfold unturn turn
  by_cases h : x+t<n
  · rw [Nat.mod_eq_of_lt h,show x+t+n-t=x+n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hx]
  · rw [Nat.mod_eq_sub_mod (by omega : n≤x+t),Nat.mod_eq_of_lt (by omega : x+t-n<n),
      show x+t-n+n-t=x by omega,Nat.mod_eq_of_lt hx]

theorem turn_unturn {n t x : ℕ} (ht : t<n) (hx : x<n) : turn n t (unturn n t x)=x := by
  unfold turn unturn
  by_cases h : x+n-t<n
  · rw [Nat.mod_eq_of_lt h,show x+n-t+t=x+n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hx]
  · rw [Nat.mod_eq_sub_mod (by omega : n≤x+n-t),Nat.mod_eq_of_lt (by omega : x+n-t-n<n),
      show x+n-t-n+t=x by omega,Nat.mod_eq_of_lt hx]

private theorem turn_rotate {n t x : ℕ} (ht : t<n) (hx : x<n) : turn n t x=rotate n x t := by
  unfold turn rotate
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega : n≤x+t),Nat.mod_eq_of_lt (by omega)]

theorem distance_turn {n t x y : ℕ} (ht : t<n) (hx : x<n) (hy : y<n) :
    distance n (turn n t x) (turn n t y)=distance n x y := by
  rw [turn_rotate ht hx,turn_rotate ht hy]
  rcases lt_trichotomy x y with h|rfl|h
  · simpa only [distance,min_eq_left h.le,max_eq_right h.le] using rotated_distance h hy ht
  · simp [distance,cyclicLength]
  · rw [distance_swap n (rotate n x t),distance_swap n x y]
    simpa only [distance,min_eq_left h.le,max_eq_right h.le] using rotated_distance h hx ht

theorem support_lt {g k ε x : ℕ} (hk : k≤2*g) (hε : ε≤1) (hx : x∈support g k ε) : x<vertexCount g := by
  unfold support at hx
  simp only [List.mem_append,List.mem_range'_1] at hx
  unfold vertexCount
  rcases hx with h|h <;> omega

def classSupport (g k c : ℕ) :=
  (support g k (parity c).val).map (turn (vertexCount g) (shift g c))

def liftPartner (g c : ℕ) (h : ℕ → ℕ) (x : ℕ) :=
  unturn (vertexCount g) (shift g c) (h (turn (vertexCount g) (shift g c) x))

theorem pullback_partners {g k c : ℕ} (hk : k≤2*g) {h : ℕ → ℕ} (p : Partners (classSupport g k c) h) :
    Partners (support g k (parity c).val) (liftPartner g c h) ∧
    ∀ x∈support g k (parity c).val,
      turn (vertexCount g) (shift g c) (liftPartner g c h x) = h (turn (vertexCount g) (shift g c) x) := by
  let n := vertexCount g
  let t := shift g c
  let W := support g k (parity c).val
  have ht : t<n := shift_lt g c
  have bound (x : ℕ) (hx : x∈W) : x<n := support_lt hk (by have := (parity c).isLt; omega) hx
  have image (x : ℕ) (hx : x∈W) : turn n t x ∈ classSupport g k c := List.mem_map.mpr ⟨x,hx,rfl⟩
  have memo (x : ℕ) (hx : x∈W) : liftPartner g c h x∈W ∧ turn n t (liftPartner g c h x)=h (turn n t x) := by
    obtain ⟨y,hy,e⟩ := List.mem_map.mp (p _ (image x hx)).1
    change turn n t y=h (turn n t x) at e
    have eq : liftPartner g c h x=y := by
      change unturn n t (h (turn n t x))=y
      rw [←e,unturn_turn ht (bound y hy)]
    exact ⟨eq ▸ hy,eq ▸ e⟩
  refine ⟨?_,fun x hx => (memo x hx).2⟩
  intro x hx
  obtain ⟨hy,e⟩ := memo x hx
  obtain ⟨_,hi,hd⟩ := p _ (image x hx)
  refine ⟨hy,?_,?_⟩
  · change unturn n t (h (turn n t (liftPartner g c h x)))=x
    rw [e,hi,unturn_turn ht (bound x hx)]
  · exact fun eq => hd ((e ▸ congrArg (turn n t) eq) : h (turn n t x)=turn n t x)

def admissibleClass (g k : ℕ) (f : Fin 2 → ℕ → ℕ) (c : ℕ) (h : ℕ → ℕ) : Prop :=
  Partners (classSupport g k c) h ∧
    ∀ x∈classSupport g k c, ∀ i : Fin 2, ∀ y∈support g k i.val,
      distance (vertexCount g) x (h x)≠distance (vertexCount g) y (f i y)

theorem admissible_pullback {g k c : ℕ} (hk : k≤2*g) {f : Fin 2 → ℕ → ℕ} {h : ℕ → ℕ}
    (ad : admissibleClass g k f c h) :
    Partners (support g k (parity c).val) (liftPartner g c h) ∧
      avoidsBase g k f (parity c) (liftPartner g c h) := by
  obtain ⟨p,e⟩ := pullback_partners hk ad.1
  refine ⟨p,?_⟩
  intro x hx i y hy eq
  have hε : (parity c).val≤1 := by have := (parity c).isLt; omega
  apply ad.2 _ (List.mem_map.mpr ⟨x,hx,rfl⟩) i y hy
  rw [← e x hx,distance_turn (shift_lt g c) (support_lt hk hε hx) (support_lt hk hε (p x hx).1)]
  exact eq

theorem both_parities (g c : ℕ) (i : Fin 2) : ∃ j : Fin 3, parity (colour g c j.val)=i := by
  have rem (j : ℕ) : (colour g c j)%2=(c+j)%2 :=
    Nat.mod_mod_of_dvd _ ⟨vertexCount g,rfl⟩
  by_cases h : c%2=i.val
  · exact ⟨0,Fin.ext ((rem 0).trans (by simpa using h))⟩
  · exact ⟨1,Fin.ext ((rem 1).trans (by have := i.isLt; omega))⟩

def OneForward (g k c : ℕ) : Prop :=
  ∃ f : Fin 2 → ℕ → ℕ, Base g k f ∧
    ∃ h : Fin 3 → ℕ → ℕ, ∀ j, admissibleClass g k f (colour g c j.val) (h j)

theorem window_supplies {g k c : ℕ} (hk : k≤2*g) {f : Fin 2 → ℕ → ℕ} {h : Fin 3 → ℕ → ℕ}
    (hw : ∀ j, admissibleClass g k f (colour g c j.val) (h j)) (i : Fin 2) :
    ∃ m, Partners (support g k i.val) m ∧ avoidsBase g k f i m := by
  obtain ⟨j,p⟩ := both_parities g c i
  exact ⟨_,p ▸ admissible_pullback hk (hw j)⟩

end CircularIndex.Insertion.Small
