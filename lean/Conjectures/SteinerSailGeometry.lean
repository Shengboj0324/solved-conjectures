import Conjectures.SteinerSailSystem

/-! A point and a transversal determine four distinct blocks on seven points.
The center and transversal can be recovered from the four blocks. -/

namespace SteinerSail.System

variable {V : Type*} [DecidableEq V]

noncomputable def spokeBlocks (S : System V) (p : V) (T : Finset V) : Finset (Finset V) :=
  T.image (S.join p)

noncomputable def sailBlocks (S : System V) (p : V) (T : Finset V) : Finset (Finset V) :=
  insert T (S.spokeBlocks p T)

noncomputable def vertices (S : System V) (p : V) (T : Finset V) : Finset V :=
  insert p (T.biUnion fun x => (S.join p x).erase p)

theorem distinct_spokes (S : System V) {p : V} {T : Finset V} (ht : T∈S.blocks) (hp : p∉T) :
    Set.InjOn (S.join p) (T : Set V) := by
  intro x hx y hy eq
  by_contra xy
  obtain ⟨b,pc,xc⟩ := S.join_spec (show p≠x from fun h => hp (h ▸ hx))
  obtain ⟨_,_,yc⟩ := S.join_spec (show p≠y from fun h => hp (h ▸ hy))
  rw [←eq] at yc
  have both := (S.join_eq xy b xc yc).symm.trans (S.join_eq xy ht hx hy)
  exact hp (both ▸ pc)

theorem spoke_block_spec (S : System V) {p : V} {T U : Finset V} (hp : p∉T)
    (hu : U∈S.spokeBlocks p T) : U∈S.blocks ∧ p∈U := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b,pc,_⟩ := S.join_spec (show p≠x from fun h => hp (h ▸ hx))
  exact ⟨b,pc⟩

theorem transversal_not_spoke (S : System V) {p : V} {T : Finset V} (hp : p∉T) : T∉S.spokeBlocks p T :=
  fun h => hp (S.spoke_block_spec hp h).2

theorem spoke_blocks_card (S : System V) {p : V} {T : Finset V} (ht : T∈S.blocks) (hp : p∉T) :
    (S.spokeBlocks p T).card=3 := by
  rw [spokeBlocks,Finset.card_image_of_injOn (S.distinct_spokes ht hp),S.triple _ ht]

theorem sail_blocks_card (S : System V) {p : V} {T : Finset V} (ht : T∈S.blocks) (hp : p∉T) :
    (S.sailBlocks p T).card=4 := by
  rw [sailBlocks,Finset.card_insert_of_notMem (S.transversal_not_spoke hp),S.spoke_blocks_card ht hp]

theorem vertices_card (S : System V) {p : V} {T : Finset V} (ht : T∈S.blocks) (hp : p∉T) :
    (S.vertices p T).card=7 := by
  have absent : p∉T.biUnion (fun x => (S.join p x).erase p) := by simp
  rw [vertices,Finset.card_insert_of_notMem absent,Finset.card_biUnion]
  · have term (x) (hx : x∈T) : ((S.join p x).erase p).card=2 := by
      obtain ⟨b,pc,_⟩ := S.join_spec (show p≠x from fun h => hp (h ▸ hx))
      rw [Finset.card_erase_of_mem pc,S.triple _ b]
    rw [Finset.sum_congr rfl term]
    simp [S.triple _ ht]
  · intro x hx y hy xy
    obtain ⟨bx,px,_⟩ := S.join_spec (show p≠x from fun h => hp (h ▸ hx))
    obtain ⟨by',py,_⟩ := S.join_spec (show p≠y from fun h => hp (h ▸ hy))
    exact S.blocks_disjoint_erased bx by' px py (fun eq => xy (S.distinct_spokes ht hp hx hy eq))

theorem vertex_iff (S : System V) {p v : V} {T : Finset V} (hp : p∉T) (vp : v≠p) :
    v∈S.vertices p T ↔ ∃ x∈(S.join p v).erase p,x∈T := by
  simp only [vertices,Finset.mem_insert,Finset.mem_biUnion,Finset.mem_erase,vp,false_or]
  constructor
  · rintro ⟨x,xt,_,vx⟩
    have xp : x≠p := fun eq => hp (eq ▸ xt)
    obtain ⟨b,pc,xc⟩ := S.join_spec xp.symm
    exact ⟨x,⟨xp,(S.join_eq vp.symm b pc vx).symm ▸ xc⟩,xt⟩
  · rintro ⟨x,⟨xp,xv⟩,xt⟩
    obtain ⟨b,pc,vc⟩ := S.join_spec vp.symm
    exact ⟨x,xt,vp,(S.join_eq xp.symm b pc xv).symm ▸ vc⟩

theorem spokes_three_iff (S : System V) (color : Finset V → Bool) {p : V} {T : Finset V} (ht : T∈S.blocks)
    (hp : p∉T) : S.spokes color p T=3 ↔ ∀ U∈S.sailBlocks p T,color U=color T := by
  change (T.filter _).card=3 ↔ _
  rw [←S.triple _ ht,Finset.card_filter_eq_iff]
  constructor
  · intro same U hU
    rcases Finset.mem_insert.mp hU with rfl|h
    · rfl
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
    exact (same x hx).2
  · intro all x hx
    exact ⟨fun eq => hp (eq ▸ hx),all _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx))⟩

theorem center_degree (S : System V) {p : V} {T : Finset V} (ht : T∈S.blocks) (hp : p∉T) :
    ((S.sailBlocks p T).filter fun B => p∈B).card=3 := by
  have eq : (S.sailBlocks p T).filter (fun B => p∈B)=S.spokeBlocks p T := by
    ext B
    simp only [sailBlocks,Finset.mem_filter,Finset.mem_insert]
    constructor
    · rintro ⟨rfl|hb,pc⟩
      · exact (hp pc).elim
      · exact hb
    · exact fun hb => ⟨Or.inr hb,(S.spoke_block_spec hp hb).2⟩
  rw [eq,S.spoke_blocks_card ht hp]

theorem noncenter_degree (S : System V) {p v : V} {T : Finset V} (hp : p∉T) (vp : v≠p) :
    ((S.sailBlocks p T).filter fun B => v∈B).card≤2 := by
  let K := (S.spokeBlocks p T).filter fun B => v∈B
  have atMost : K.card≤1 := by
    apply Finset.card_le_one.mpr
    intro A ha B hb
    obtain ⟨sa,va⟩ := Finset.mem_filter.mp ha
    obtain ⟨sb,vb⟩ := Finset.mem_filter.mp hb
    obtain ⟨ba,pa⟩ := S.spoke_block_spec hp sa
    obtain ⟨bb,pb⟩ := S.spoke_block_spec hp sb
    exact (S.join_eq vp ba va pa).symm.trans (S.join_eq vp bb vb pb)
  have sub : (S.sailBlocks p T).filter (fun B => v∈B)⊆insert T K := by
    intro B hb
    obtain ⟨su,mem⟩ := Finset.mem_filter.mp hb
    rcases Finset.mem_insert.mp su with rfl|su
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨su,mem⟩)
  exact (Finset.card_le_card sub).trans ((Finset.card_insert_le _ _).trans (by omega))

theorem unique_sail (S : System V) {p q : V} {T U : Finset V}
    (ht : T∈S.blocks) (pt : p∉T) (qu : q∉U) (eq : S.sailBlocks p T=S.sailBlocks q U) :
    p=q ∧ T=U := by
  have pc : p=q := by
    by_contra ne
    have high := S.center_degree ht pt
    rw [eq] at high
    have low := S.noncenter_degree qu ne
    omega
  subst q
  have member : T∈S.sailBlocks p U := eq ▸ Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp member with same|spoke
  · exact ⟨rfl,same⟩
  · exact (pt (S.spoke_block_spec qu spoke).2).elim

end SteinerSail.System
