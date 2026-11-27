import Conjectures.SteinerSailDegrees
import Conjectures.SteinerSailParity

/-! Mixed pairs of neighbors are counted by their unique block. -/

namespace SteinerSail.System

variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def inside (S : System V) (color : Finset V → Bool) (p : V) (T : Finset V) (c : Bool) : ℕ :=
  ((S.neighbors color p c) ∩ T).card

theorem inside_spokes (S : System V) (color : Finset V → Bool) (p : V) (T : Finset V) :
    S.inside color p T (color T)=S.spokes color p T := by
  unfold inside spokes
  congr 1
  ext x
  simp [neighbors,and_comm,and_left_comm,ne_comm]

theorem inside_sum (S : System V) (color : Finset V → Bool) (p : V) (T : Finset V) :
    S.inside color p T true + S.inside color p T false = (T.erase p).card := by
  have dis := (S.neighbor_colors_disjoint color p).mono (Finset.inter_subset_left (s₂ := T))
    (Finset.inter_subset_left (s₂ := T))
  rw [inside,inside,←Finset.card_union_of_disjoint dis,←Finset.union_inter_distrib_right,S.neighbor_colors_union]
  congr 1
  ext x
  simp

theorem sum_inside_products (S : System V) (color : Finset V → Bool) (p : V) :
    (∑ T∈S.blocks,S.inside color p T true*S.inside color p T false)=
      S.degree color p true*S.degree color p false := by
  let R := S.neighbors color p true
  let B := S.neighbors color p false
  have ne {x y : V} (hx : x∈R) (hy : y∈B) : x≠y := by
    rintro rfl
    exact Finset.disjoint_left.mp (S.neighbor_colors_disjoint color p) hx hy
  have fiber (T : Finset V) (ht : T∈S.blocks) :
      (R ×ˢ B).filter (fun q => S.join q.1 q.2=T) = (R∩T) ×ˢ (B∩T) := by
    ext ⟨x,y⟩
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_inter]
    constructor
    · rintro ⟨⟨hx,hy⟩,eq⟩
      obtain ⟨_,xt,yt⟩ := S.join_spec (ne hx hy)
      exact ⟨⟨hx,eq ▸ xt⟩,hy,eq ▸ yt⟩
    · rintro ⟨⟨hx,xt⟩,hy,yt⟩
      exact ⟨⟨hx,hy⟩,S.join_eq (ne hx hy) ht xt yt⟩
  have maps : (R ×ˢ B).filter (fun q => S.join q.1 q.2∈S.blocks)=R ×ˢ B := by
    apply Finset.filter_true_of_mem
    intro q hq
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hq
    exact (S.join_spec (ne hx hy)).1
  have count := Finset.sum_card_fiberwise_eq_card_filter (R ×ˢ B) S.blocks (fun q => S.join q.1 q.2)
  rw [maps,Finset.card_product] at count
  change _=R.card*B.card
  rw [←count]
  apply Finset.sum_congr rfl
  intro T ht
  rw [fiber T ht,Finset.card_product]
  rfl

noncomputable def outsideSum (S : System V) (f : V → Finset V → ℕ) : ℕ :=
  ∑ p : V,∑ T∈S.blocks, if p∈T then 0 else f p T

theorem frequency_eq (S : System V) (color : Finset V → Bool) (j : ℕ) :
    S.frequency color j=S.outsideSum (fun p T => if S.spokes color p T=j then 1 else 0) := by
  simp only [frequency,outside,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product,outsideSum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro T _
  by_cases hp : p∈T <;> simp [hp]

theorem inside_product (S : System V) (color : Finset V → Bool) (p : V) {T : Finset V} (ht : T∈S.blocks) :
    S.inside color p T true*S.inside color p T false =
      if p∈T then 0 else S.spokes color p T*(3-S.spokes color p T) := by
  have total := S.inside_sum color p T
  have eq := S.inside_spokes color p T
  by_cases hp : p∈T
  · simp only [hp,ite_true]
    rw [Finset.card_erase_of_mem hp,S.triple _ ht] at total
    have hj := S.incident_spokes color ht hp
    cases hc : color T <;> rw [hc,hj] at eq <;> simp_all
  · simp only [hp,ite_false]
    rw [Finset.erase_eq_of_notMem hp,S.triple _ ht] at total
    cases hc : color T
    · rw [hc] at eq
      have h : 3-S.spokes color p T=S.inside color p T true := by omega
      rw [h,←eq,mul_comm]
    · rw [hc] at eq
      have h : 3-S.spokes color p T=S.inside color p T false := by omega
      rw [h,←eq]

theorem mixed_spoke_count (S : System V) (color : Finset V → Bool) :
    S.outsideSum (S.spokes color)+S.frequency color 1=
      (∑ p : V,S.degree color p true*S.degree color p false)+3*S.frequency color 3 := by
  simp only [frequency_eq,outsideSum,←sum_inside_products,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro T ht
  rw [S.inside_product color p ht]
  by_cases hp : p∈T
  · simp [hp]
  · simpa [hp] using spoke_identity (S.spokes_le color ht p)

end SteinerSail.System
