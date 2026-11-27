import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! A Steiner triple system is a finite family of triples with exactly one
block through each pair of distinct points. Sails are indexed by an outside
point and a transversal block. -/

namespace SteinerSail

variable {V : Type*} [DecidableEq V]

structure System (V : Type*) [DecidableEq V] where
  blocks : Finset (Finset V)
  triple : ∀ T∈blocks,T.card=3
  one : ∀ x y : V,x≠y → ∃! T : Finset V,T∈blocks ∧ x∈T ∧ y∈T

namespace System

noncomputable def join (S : System V) (x y : V) : Finset V :=
  if h : x=y then ∅ else Classical.choose (S.one x y h).exists

theorem join_spec (S : System V) {x y : V} (xy : x≠y) :
    S.join x y∈S.blocks ∧ x∈S.join x y ∧ y∈S.join x y := by
  simpa [join,xy] using Classical.choose_spec (S.one x y xy).exists

theorem join_eq (S : System V) {x y : V} (xy : x≠y) {T : Finset V}
    (hT : T∈S.blocks) (hx : x∈T) (hy : y∈T) : S.join x y=T :=
  (S.one x y xy).unique (S.join_spec xy) ⟨hT,hx,hy⟩

theorem join_comm (S : System V) (x y : V) : S.join x y=S.join y x := by
  by_cases eq : x=y
  · rw [eq]
  obtain ⟨ht,hy,hx⟩ := S.join_spec (Ne.symm eq)
  exact S.join_eq eq ht hx hy

def through (S : System V) (color : Finset V → Bool) (x : V) (c : Bool) : Finset (Finset V) :=
  S.blocks.filter fun T => x∈T ∧ color T=c

noncomputable def neighbors [Fintype V] (S : System V) (color : Finset V → Bool) (x : V) (c : Bool) : Finset V :=
  Finset.univ.filter fun y => x≠y ∧ color (S.join x y)=c

theorem neighbors_union [Fintype V] (S : System V) (color : Finset V → Bool) (x : V) (c : Bool) :
    S.neighbors color x c=(S.through color x c).biUnion (fun T => T.erase x) := by
  ext y
  simp only [neighbors,through,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion,Finset.mem_erase]
  constructor
  · rintro ⟨xy,co⟩
    obtain ⟨ht,hx,hy⟩ := S.join_spec xy
    exact ⟨S.join x y,⟨ht,hx,co⟩,xy.symm,hy⟩
  · rintro ⟨T,⟨ht,hx,co⟩,yx,hy⟩
    exact ⟨yx.symm,(S.join_eq yx.symm ht hx hy) ▸ co⟩

theorem blocks_disjoint_erased (S : System V) {T U : Finset V} (ht : T∈S.blocks) (hu : U∈S.blocks)
    {x : V} (xt : x∈T) (xu : x∈U) (ne : T≠U) : Disjoint (T.erase x) (U.erase x) := by
  apply Finset.disjoint_left.mpr
  intro y yt yu
  obtain ⟨yx,tp⟩ := Finset.mem_erase.mp yt
  exact ne ((S.join_eq yx.symm ht xt tp).symm.trans (S.join_eq yx.symm hu xu (Finset.mem_erase.mp yu).2))

theorem neighbor_degree [Fintype V] (S : System V) (color : Finset V → Bool) (x : V) (c : Bool) :
    (S.neighbors color x c).card=2*(S.through color x c).card := by
  rw [neighbors_union,Finset.card_biUnion]
  · have term (T) (mem : T∈S.through color x c) : (T.erase x).card=2 := by
      obtain ⟨ht,hx,_⟩ := Finset.mem_filter.mp mem
      rw [Finset.card_erase_of_mem hx,S.triple _ ht]
    rw [Finset.sum_congr rfl term]
    simp [mul_comm]
  · intro T ht U hu ne
    obtain ⟨t,xt,_⟩ := Finset.mem_filter.mp ht
    obtain ⟨u,xu,_⟩ := Finset.mem_filter.mp hu
    exact S.blocks_disjoint_erased t u xt xu ne

def outside [Fintype V] (S : System V) : Finset (V × Finset V) :=
  (Finset.univ ×ˢ S.blocks).filter fun p => p.1∉p.2

noncomputable def spokes (S : System V) (color : Finset V → Bool) (p : V) (T : Finset V) : ℕ :=
  (T.filter fun x => x≠p ∧ color (S.join p x)=color T).card

noncomputable def frequency [Fintype V] (S : System V) (color : Finset V → Bool) (j : ℕ) : ℕ :=
  (S.outside.filter fun q => S.spokes color q.1 q.2=j).card

theorem spokes_le (S : System V) (color : Finset V → Bool) {T : Finset V} (ht : T∈S.blocks) (p : V) :
    S.spokes color p T≤3 := (Finset.card_filter_le _ _).trans_eq (S.triple _ ht)

theorem incident_spokes (S : System V) (color : Finset V → Bool) {p : V} {T : Finset V}
    (ht : T∈S.blocks) (hp : p∈T) : S.spokes color p T=2 := by
  have same : T.filter (fun x => x≠p ∧ color (S.join p x)=color T)=T.erase p := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_erase]
    constructor
    · rintro ⟨xt,xp,_⟩; exact ⟨xp,xt⟩
    · rintro ⟨xp,xt⟩; exact ⟨xt,xp,congrArg color (S.join_eq xp.symm ht hp xt)⟩
  rw [spokes,same,Finset.card_erase_of_mem hp,S.triple _ ht]

end System
end SteinerSail
