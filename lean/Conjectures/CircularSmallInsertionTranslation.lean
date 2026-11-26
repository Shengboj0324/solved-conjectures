import Conjectures.CircularSmallInsertionForced

/-! At 31 vertices, adding two to the colour translates every labelled edge
by 21. Consequently two reference starting parities cover all 62 colours. -/

namespace CircularIndex.Insertion.Small

def moveEdge (t : ℕ) (e : ℕ × ℕ) := edge (turn 31 t e.1) (turn 31 t e.2)

private theorem move_edge (t x y : ℕ) : moveEdge t (edge x y)=edge (turn 31 t x) (turn 31 t y) := by
  rcases le_total x y with h|h
  · simp only [moveEdge,edge,min_eq_left h,max_eq_right h]
  · rw [edge_swap x y,show edge y x=(y,x) from by simp [edge,min_eq_left h,max_eq_right h]]
    apply edge_swap

private theorem move_label (x c d t j : ℕ) (eq : d%62=(c+2*t)%62) :
    turn 31 (shift 5 (colour 5 d j)) x =
      turn 31 (21*t) (turn 31 (shift 5 (colour 5 c j)) x) := by
  change (x+((21*((d+j)%62))%62)/2)%31 = ((x+((21*((c+j)%62))%62)/2)%31+21*t)%31
  have add : (d+j)%62=(c+j+2*t)%62 := by
    rw [←Nat.mod_add_mod d 62 j,eq,Nat.mod_add_mod]
    congr 1
    omega
  rw [add]
  simp only [Nat.mul_mod_mod]
  rw [Nat.mod_mul_right_div_self _ 2 31,Nat.mod_mul_right_div_self _ 2 31,
    show 21*(c+j+2*t)=21*(c+j)+2*(21*t) by omega,
    Nat.add_mul_div_left _ _ (by decide)]
  simp only [Nat.add_mod_mod,Nat.mod_add_mod,Nat.add_assoc]

private theorem move_parity (c d t j : ℕ) (eq : d%62=(c+2*t)%62) :
    parity (colour 5 c j)=parity (colour 5 d j) := by
  apply Fin.ext
  change ((c+j)%62)%2=((d+j)%62)%2
  omega

theorem move_block {c d t : ℕ} (eq : d%62=(c+2*t)%62) (M : MatchPair) {e : ℕ × ℕ}
    (he : e∈forcedBlock 5 c M) : moveEdge (21*t) e∈forcedBlock 5 d M := by
  obtain ⟨j,hj,hm⟩ := List.mem_flatMap.mp he
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hm
  refine List.mem_flatMap.mpr ⟨j,hj,List.mem_map.mpr ⟨b,?_,?_⟩⟩
  · change b∈entry M (parity (colour 5 d j.val))
    rwa [←move_parity _ _ _ _ eq]
  · change edge (turn 31 (shift 5 (colour 5 d j.val)) b.1) (turn 31 (shift 5 (colour 5 d j.val)) b.2) =
      moveEdge (21*t) (edge (turn 31 (shift 5 (colour 5 c j.val)) b.1) (turn 31 (shift 5 (colour 5 c j.val)) b.2))
    rw [move_edge,move_label _ c d t j.val eq,move_label _ c d t j.val eq]

def overlap (X Y : Matching) : Bool := X.any fun e => decide (e∈Y)

theorem overlap_iff (X Y : Matching) : overlap X Y=true ↔ ∃ e∈X, e∈Y := by
  simp [overlap,List.any_eq_true]

def allowedGap (q p d : ℕ) : Prop :=
  (23≤d ∧ d≤39) ∨ (d=17 ∧ p=q) ∨ (d=45 ∧ p≠q)

instance (q p d : ℕ) : Decidable (allowedGap q p d) := by unfold allowedGap; infer_instance

def refChecks (q : ℕ) (M : MatchPair) : Bool :=
  (List.range 2).all fun p => (List.range 62).all fun d =>
    decide (allowedGap q p d) || overlap (forcedBlock 5 p M) (forcedBlock 5 (p+d) M)

theorem disjoint_gap {M : MatchPair} {q : ℕ} (checked : refChecks q M=true)
    (c d : Fin 62) (dis : ∀ e∈forcedBlock 5 c.val M, e∉forcedBlock 5 d.val M) :
    allowedGap q (c.val%2) ((d.val+62-c.val)%62) := by
  let p := c.val%2
  let r := (d.val+62-c.val)%62
  have h₁ : p<2 := Nat.mod_lt _ (by decide)
  have h₂ : r<62 := Nat.mod_lt _ (by decide)
  have eq := List.all_eq_true.mp (List.all_eq_true.mp checked p (List.mem_range.mpr h₁)) r (List.mem_range.mpr h₂)
  rcases Bool.or_eq_true_iff.mp eq with yes|meet
  · exact of_decide_eq_true yes
  · obtain ⟨e,he,he'⟩ := (overlap_iff ..).mp meet
    have cEq : c.val%62=(p+2*(c.val/2))%62 := by dsimp [p]; omega
    have dEq : d.val%62=(p+r+2*(c.val/2))%62 := by
      dsimp [p,r]
      have := c.isLt
      have := d.isLt
      omega
    exact False.elim (dis _ (move_block cEq M he) (move_block dEq M he'))

/-- Three pairwise compatible starts would force a cycle on the allowed
differences. Two gaps of 17 would have to start at opposite parities. -/
theorem no_gap_triangle {q : ℕ} (hq : q<2) (a b c : Fin 62)
    (ab : allowedGap q (a.val%2) ((b.val+62-a.val)%62))
    (bc : allowedGap q (b.val%2) ((c.val+62-b.val)%62))
    (ca : allowedGap q (c.val%2) ((a.val+62-c.val)%62)) : False := by
  have := a.isLt
  have := b.isLt
  have := c.isLt
  unfold allowedGap at ab bc ca
  omega

end CircularIndex.Insertion.Small
