import Conjectures.SteinerSailDegrees
import Conjectures.SteinerSailParity

/-! An odd point--block pair witnesses every disjoint red--blue block pair. -/

namespace SteinerSail.System

variable {V : Type*} [DecidableEq V] [Fintype V]

def incident (S : System V) (x : V) : Finset (Finset V) := S.blocks.filter fun T => x∈T

omit [Fintype V] in
theorem through_total (S : System V) (color : Finset V → Bool) (x : V) :
    (S.through color x true).card+(S.through color x false).card=(S.incident x).card := by
  have cut := Finset.card_filter_add_card_filter_not (s := S.incident x) (p := fun T => color T=true)
  simpa only [incident,through,Finset.filter_filter,Bool.not_eq_true] using cut

theorem twice_incident (S : System V) (color : Finset V → Bool) (x : V) :
    2*(S.incident x).card=Fintype.card V-1 := by
  rw [←S.through_total color,Nat.mul_add,←S.neighbor_degree color x true,←S.neighbor_degree color x false]
  exact S.degree_sum_point color x

omit [Fintype V] in
theorem spokes_subtype (S : System V) (color : Finset V → Bool) (p : V) {T : Finset V} (hp : p∉T) :
    S.spokes color p T=∑ x : T,if color (S.join p x)=color T then 1 else 0 := by
  rw [Finset.sum_coe_sort T (fun x : V => if color (S.join p x)=color T then (1 : ℕ) else 0),spokes,Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  have xne : x≠p := fun h => hp (h ▸ hx)
  simp [xne]

omit [Fintype V] in
theorem opposite_witness (S : System V) (color : Finset V → Bool) {T U : Finset V}
    (ht : T∈S.blocks) (hu : U∈S.blocks) (red : color T=true) (blue : color U=false) (dis : Disjoint T U) :
    (∃ p∈U, Odd (S.spokes color p T)) ∨ (∃ p∈T, Odd (S.spokes color p U)) := by
  have toOdd (B : Finset V) (hb : B∈S.blocks) : Odd (Fintype.card B) := by
    rw [Fintype.card_coe,S.triple _ hb]
    decide
  have witness := opposite_array (toOdd U hu) (toOdd T ht) (fun p x => color (S.join (p : V) (x : V)))
  rcases witness with ⟨p,hp⟩|⟨p,hp⟩
  · left
    refine ⟨p,p.property,?_⟩
    rw [S.spokes_subtype color p (fun h => Finset.disjoint_left.mp dis h p.property),red]
    exact hp
  · right
    refine ⟨p,p.property,?_⟩
    rw [S.spokes_subtype color p (Finset.disjoint_left.mp dis p.property),blue]
    convert hp using 2
    rename_i y _
    rw [S.join_comm (p : V) (y : V)]
    cases color (S.join (y : V) (p : V)) <;> rfl

noncomputable def oddPairs (S : System V) (color : Finset V → Bool) : Finset (V × Finset V) :=
  S.outside.filter fun q => Odd (S.spokes color q.1 q.2)

theorem odd_card (S : System V) (color : Finset V → Bool) :
    (S.oddPairs color).card=S.frequency color 1+S.frequency color 3 := by
  let f (j : ℕ) := S.outside.filter fun q => S.spokes color q.1 q.2=j
  have dis : Disjoint (f 1) (f 3) := by
    apply Finset.disjoint_left.mpr
    intro q h1 h3
    have h := (Finset.mem_filter.mp h1).2
    have h' := (Finset.mem_filter.mp h3).2
    omega
  have union : S.oddPairs color=f 1 ∪ f 3 := by
    ext q
    simp only [oddPairs,f,Finset.mem_filter,Finset.mem_union]
    constructor
    · rintro ⟨out,odd⟩
      have ht := (Finset.mem_product.mp (Finset.mem_filter.mp out).1).2
      have bound := S.spokes_le color ht q.1
      obtain ⟨k,hk⟩ := odd
      by_cases h : S.spokes color q.1 q.2=1
      · exact Or.inl ⟨out,h⟩
      · exact Or.inr ⟨out,by omega⟩
    · rintro (⟨out,one⟩|⟨out,three⟩)
      · exact ⟨out,one ▸ (by decide : Odd 1)⟩
      · exact ⟨out,three ▸ (by decide : Odd 3)⟩
  rw [union,Finset.card_union_of_disjoint dis]
  rfl

end SteinerSail.System
