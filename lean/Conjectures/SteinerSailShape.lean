import Conjectures.SteinerSailGeometry

/-! Identify the vertex support with the literal union of the four blocks
and their intersections with one another. -/

namespace SteinerSail.System

variable {V : Type*} [DecidableEq V]

theorem vertex_union (S : System V) {p : V} {T : Finset V} (ht : T∈S.blocks) (hp : p∉T) :
    S.vertices p T=(S.sailBlocks p T).biUnion id := by
  ext v
  constructor
  · intro member
    rcases Finset.mem_insert.mp member with eq|h
    · subst v
      obtain ⟨x,xt⟩ := Finset.card_pos.mp (show 0<T.card by rw [S.triple _ ht]; decide)
      have px : p≠x := fun eq => hp (eq ▸ xt)
      exact Finset.mem_biUnion.mpr ⟨S.join p x,Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ xt),(S.join_spec px).2.1⟩
    · obtain ⟨x,xt,vx⟩ := Finset.mem_biUnion.mp h
      exact Finset.mem_biUnion.mpr ⟨S.join p x,Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ xt),(Finset.mem_erase.mp vx).2⟩
  · intro member
    obtain ⟨B,hB,vb⟩ := Finset.mem_biUnion.mp member
    by_cases vp : v=p
    · exact Finset.mem_insert.mpr (Or.inl vp)
    apply Finset.mem_insert_of_mem
    rcases Finset.mem_insert.mp hB with rfl|h
    · exact Finset.mem_biUnion.mpr ⟨v,vb,Finset.mem_erase.mpr ⟨vp,(S.join_spec (Ne.symm vp)).2.2⟩⟩
    · obtain ⟨x,xt,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_biUnion.mpr ⟨x,xt,Finset.mem_erase.mpr ⟨vp,vb⟩⟩

theorem spokes_intersection (S : System V) {p x y : V} {T : Finset V}
    (ht : T∈S.blocks) (hp : p∉T) (hx : x∈T) (hy : y∈T) (xy : x≠y) :
    S.join p x ∩ S.join p y={p} := by
  have px : p≠x := fun h => hp (h ▸ hx)
  have py : p≠y := fun h => hp (h ▸ hy)
  obtain ⟨bx,pc,_⟩ := S.join_spec px
  obtain ⟨by',pd,_⟩ := S.join_spec py
  have dis := S.blocks_disjoint_erased bx by' pc pd (fun eq => xy (S.distinct_spokes ht hp hx hy eq))
  ext v
  simp only [Finset.mem_inter,Finset.mem_singleton]
  constructor
  · rintro ⟨vx,vy⟩
    by_contra ne
    exact Finset.disjoint_left.mp dis (Finset.mem_erase.mpr ⟨ne,vx⟩) (Finset.mem_erase.mpr ⟨ne,vy⟩)
  · rintro rfl
    exact ⟨pc,pd⟩

theorem transversal_intersection (S : System V) {p x : V} {T : Finset V}
    (ht : T∈S.blocks) (hp : p∉T) (hx : x∈T) : T ∩ S.join p x={x} := by
  obtain ⟨b,pc,xc⟩ := S.join_spec (show p≠x from fun h => hp (h ▸ hx))
  ext v
  simp only [Finset.mem_inter,Finset.mem_singleton]
  constructor
  · rintro ⟨vt,vx⟩
    by_contra ne
    have join := (S.join_eq ne b vx xc).symm.trans (S.join_eq ne ht vt hx)
    exact hp (join ▸ pc)
  · rintro rfl
    exact ⟨hx,xc⟩

end SteinerSail.System
