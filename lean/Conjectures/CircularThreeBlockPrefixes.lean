import Conjectures.CircularThreeBlockGraphs

/-! Keep only the first one or two inserted blocks of the same labelled
three-block graph. The proof reindexes its edges and checks the new windows. -/

namespace CircularIndex.Insertion.ThreeBlock.Prefix

open ThreeBlock

def liftColour (b c : ℕ) :=
  if b=1 then if c<9 then c else if c<15 then c+3 else c+6
  else if c<18 then c else c+3

private theorem lift_lt {g b c : ℕ} (hb : b=1 ∨ b=2) (hc : c<classCount g b) :
    liftColour b c<colours g := by
  unfold liftColour classCount colours at *
  split_ifs <;> omega

private theorem lift_inj {b c d : ℕ} (h : liftColour b c=liftColour b d) : c=d := by
  unfold liftColour at h
  split_ifs at h <;> omega

theorem lift_reference {b : ℕ} (hb : b=1 ∨ b=2) (c : ℕ) :
    ThreeBlock.reference (liftColour b c)=Insertion.reference b c := by
  unfold liftColour ThreeBlock.reference Insertion.reference
  split_ifs <;> omega

theorem keeps_blocks {b : ℕ} (hb : b=1 ∨ b=2) (c : ℕ) :
    ¬lastBlock (liftColour b c) ∧ (unitBlock (liftColour b c) ↔ added b c) := by
  unfold lastBlock unitBlock added liftColour
  split_ifs <;> omega

private theorem preserve_window {g b c d i j : ℕ} {K : Packing g} (hg : 15≤g) (hb : b=1 ∨ b=2)
    (hc : c<classCount g b) (hd : d<classCount g b) (hi : i<g) (hj : j<g)
    (hn : Near (classCount g b) c d) :
    ¬ Meeting (ThreeBlock.rotatedPair g K (liftColour b c) i) (ThreeBlock.rotatedPair g K (liftColour b d) j) := by
  obtain ⟨_,_,h₁,h₂⟩ := ThreeBlock.rawPair_spec (K := K) (c := liftColour b c) hg hi
  obtain ⟨_,_,h₃,h₄⟩ := ThreeBlock.rawPair_spec (K := K) (c := liftColour b d) hg hj
  have ac := ThreeBlock.reference_lt hg (lift_lt hb hc)
  have ad := ThreeBlock.reference_lt hg (lift_lt hb hd)
  have sep {x y : ℕ} (hx : ThreeBlock.Support g (ThreeBlock.kind (liftColour b c)) x)
      (hy : ThreeBlock.Support g (ThreeBlock.kind (liftColour b d)) y) :
      rotate (vertexCount g) x (baseShift g (ThreeBlock.reference (liftColour b c))) ≠
      rotate (vertexCount g) y (baseShift g (ThreeBlock.reference (liftColour b d))) := by
    rcases Insertion.near_reference (by omega) hb hc hd hn with h|h
    · exact ThreeBlock.near_base_disjoint hg ac (by simpa only [lift_reference hb] using h) hx hy
    · exact (ThreeBlock.near_base_disjoint hg ad (by simpa only [lift_reference hb] using h) hy hx).symm
  rintro (h|h|h|h)
  · exact sep h₁ h₃ h
  · exact sep h₁ h₄ h
  · exact sep h₂ h₃ h
  · exact sep h₂ h₄ h

private theorem near_of_small {p : ℕ} [NeZero p] (hp : 3≤p) {c d : Fin p}
    (hne : c≠d) (hlt : ((d.val : ZMod p)-(c.val : ZMod p)).val < 3) :
    Near p c.val d.val := by
  let k := ((d.val : ZMod p)-(c.val : ZMod p)).val
  have he : (c.val+k)%p = d.val := by
    have eqn : (c.val : ZMod p) + ((d.val : ZMod p)-(c.val : ZMod p)) = (d.val : ZMod p) := by abel
    have eqv := congrArg ZMod.val eqn
    rw [ZMod.val_add,ZMod.val_natCast_of_lt c.isLt,ZMod.val_natCast_of_lt d.isLt] at eqv
    exact eqv
  have hk : k < 3 := hlt
  have hc := c.isLt
  have hdiff : c.val≠d.val := fun h => hne (Fin.ext h)
  unfold Near
  by_cases h : c.val+k < p
  · rw [Nat.mod_eq_of_lt h] at he
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : p≤c.val+k),Nat.mod_eq_of_lt (by omega)] at he
    omega


section
variable {g b : ℕ} (hg : 15≤g) (hb : b=1 ∨ b=2) (K : Packing g)

def liftIndex (i : Fin (classCount g b) × Fin g) : Fin (colours g) × Fin g :=
  (⟨liftColour b i.1.val,lift_lt hb i.1.isLt⟩,i.2)

noncomputable def retained : ClassSchedule (vertexCount g) (classCount g b) g where
  pair i := scheduledPair hg K (liftIndex hb i)
  loopless i := scheduledPair_loopless hg K (liftIndex hb i)
  pairs_injective i j h := by
    have eq := scheduledPair_inj hg K h
    apply Prod.ext
    · exact Fin.ext (lift_inj (congrArg (fun z : Fin (colours g) × Fin g => z.1.val) eq))
    · exact congrArg (fun z : Fin (colours g) × Fin g => z.2) eq
  separated i j hne meet := by
    have hm := scheduledPair_meeting hg K (liftIndex hb i) (liftIndex hb j) meet
    by_cases eq : i.1=j.1
    · change Meeting (rotatedPair g K (liftColour b i.1.val) i.2.val)
        (rotatedPair g K (liftColour b j.1.val) j.2.val) at hm
      rw [←eq] at hm
      exact False.elim (hne (Prod.ext eq (Fin.ext (ThreeBlock.same_class_matching hg
        (lift_lt hb i.1.isLt) i.2.isLt j.2.isLt hm))))
    · have hp : 3≤classCount g b := by unfold classCount vertexCount; omega
      let _ : NeZero (classCount g b) := ⟨by omega⟩
      by_contra! hlt
      exact preserve_window hg hb i.1.isLt j.1.isLt i.2.isLt j.2.isLt (near_of_small hp eq hlt) hm

theorem edges_retained : (retained hg hb K).graph.edgeSet ⊆ (ThreeBlock.schedule hg K).graph.edgeSet := by
  rw [ClassSchedule.edgeSet_eq,ClassSchedule.edgeSet_eq]
  rintro e ⟨i,rfl⟩
  exact ⟨liftIndex hb i,rfl⟩

theorem degree_and_index :
    let S := retained hg hb K
    (∀ v, S.graph.degree v ≤ 4*g+b) ∧ (∃ v, S.graph.degree v = 4*g+b) ∧
      circularChromaticIndex S.graph = ((4*g+b : ℕ) : ℝ)+2/3 := by
  let S := retained hg hb K
  have hp : 3≤classCount g b := by unfold classCount vertexCount; omega
  have hp' : classCount g b=3*(4*g+b)+2 := by unfold classCount vertexCount; omega
  let _ : NeZero (classCount g b) := ⟨by omega⟩
  have avg : vertexCount g*(4*g+b-1)<2*(classCount g b*g) := by
    rcases hb with rfl|rfl <;> unfold classCount vertexCount <;>
      simp only [Nat.add_sub_cancel,show 4*g+2-1=4*g+1 by omega] <;> nlinarith
  have deg := S.max_degree _ hp' hp avg
  refine ⟨deg.1,deg.2,?_⟩
  rw [S.exact_index (by omega) rfl hp,hp']
  push_cast
  ring

end
end CircularIndex.Insertion.ThreeBlock.Prefix
