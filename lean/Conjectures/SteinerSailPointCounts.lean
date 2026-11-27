import Conjectures.SteinerSailCount
import Conjectures.SteinerSailGeometry

/-! Count the sails containing each vertex, with its center fixed first. -/

namespace SteinerSail.System

variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def transversals (S : System V) (p v : V) : Finset (Finset V) :=
  S.blocks.filter fun T => p∉T ∧ v∈S.vertices p T

theorem center_transversals (S : System V) (v : V) (hn : 3≤Fintype.card V) :
    6*(S.transversals v v).card=(Fintype.card V-1)*(Fintype.card V-3) := by
  have part := Finset.card_filter_add_card_filter_not (s := S.blocks) (p := fun T => v∈T)
  have eq : S.transversals v v=S.blocks.filter fun T => v∉T := by ext; simp [transversals,vertices]
  rw [eq]
  have inc := S.twice_incident (fun _ => true) v
  have blocks := S.block_count (fun _ => true)
  rw [S.all_blocks_card] at blocks
  unfold incident at inc
  have rel : Fintype.card V-3+3=Fintype.card V := by omega
  have arith : Fintype.card V*(Fintype.card V-1)=
      (Fintype.card V-1)*(Fintype.card V-3)+3*(Fintype.card V-1) := by
    calc
      _ = (Fintype.card V-3+3)*(Fintype.card V-1) := by rw [rel]
      _ = _ := by ring
  omega

theorem other_transversals (S : System V) {p v : V} (vp : v≠p) :
    (S.transversals p v).card=Fintype.card V-3 := by
  let J := S.join p v
  obtain ⟨bj,pj,_⟩ := S.join_spec vp.symm
  have dx : (J.erase p).card=2 := by rw [Finset.card_erase_of_mem pj,S.triple _ bj]
  let allowed (x : V) := (S.incident x).erase J
  have eq : S.transversals p v=(J.erase p).biUnion allowed := by
    ext T
    simp only [transversals,Finset.mem_filter,Finset.mem_biUnion,allowed,incident,Finset.mem_erase]
    constructor
    · rintro ⟨bt,pt,member⟩
      obtain ⟨x,hx,xt⟩ := (S.vertex_iff pt vp).mp member
      exact ⟨x,Finset.mem_erase.mp hx,fun eq => pt (eq ▸ pj),bt,xt⟩
    · rintro ⟨x,⟨xp,xj⟩,ne,bt,xt⟩
      have pt : p∉T := by
        intro pt
        exact ne ((S.join_eq xp.symm bt pt xt).symm.trans (S.join_eq xp.symm bj pj xj))
      exact ⟨bt,pt,(S.vertex_iff pt vp).mpr ⟨x,Finset.mem_erase.mpr ⟨xp,xj⟩,xt⟩⟩
  have dis : (↑(J.erase p) : Set V).PairwiseDisjoint allowed := by
    intro x hx y hy ne
    apply Finset.disjoint_left.mpr
    intro T ht hu
    obtain ⟨nj,hxt⟩ := Finset.mem_erase.mp ht
    obtain ⟨bt,xt⟩ := Finset.mem_filter.mp hxt
    have yt := (Finset.mem_filter.mp (Finset.mem_erase.mp hu).2).2
    exact nj ((S.join_eq ne bt xt yt).symm.trans
      (S.join_eq ne bj (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hy).2))
  have term (x : V) (hx : x∈J.erase p) : 2*(allowed x).card=Fintype.card V-3 := by
    have jmem : J∈S.incident x := Finset.mem_filter.mpr ⟨bj,(Finset.mem_erase.mp hx).2⟩
    have deg := S.twice_incident (fun _ => true) x
    have pos := Finset.card_pos.mpr ⟨J,jmem⟩
    change 2*((S.incident x).erase J).card=Fintype.card V-3
    rw [Finset.card_erase_of_mem jmem]
    omega
  rw [eq,Finset.card_biUnion dis]
  have twice : 2*(∑ x∈J.erase p,(allowed x).card)=2*(Fintype.card V-3) := by
    rw [Finset.mul_sum,Finset.sum_congr rfl term,Finset.sum_const,dx]
    simp
  omega

theorem point_incidence (S : System V) (v : V) (hn : 3≤Fintype.card V) :
    6*(S.outside.filter fun q => v∈S.vertices q.1 q.2).card =
      7*(Fintype.card V-1)*(Fintype.card V-3) := by
  have count : (S.outside.filter fun q => v∈S.vertices q.1 q.2).card=
      ∑ p : V,(S.transversals p v).card := by
    simp only [outside,transversals,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro T _
    by_cases pt : p∈T <;> simp [pt]
  rw [count,←Finset.sum_erase_add _ _ (Finset.mem_univ v),Nat.mul_add,S.center_transversals v hn]
  have term (p : V) (hp : p∈Finset.univ.erase v) : (S.transversals p v).card=Fintype.card V-3 :=
    S.other_transversals (Finset.mem_erase.mp hp).1.symm
  rw [Finset.sum_congr rfl term,Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ v),Finset.card_univ]
  simp only [nsmul_eq_mul,Nat.cast_id]
  ring

end SteinerSail.System
