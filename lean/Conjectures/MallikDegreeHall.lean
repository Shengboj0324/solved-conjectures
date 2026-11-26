import Conjectures.MallikDegreeGraphs
import Mathlib.Combinatorics.Hall.Basic

/-! Prove the direction of the bipartite expansion criterion used here by
removing a prescribed matching and applying Hall to the remaining vertices. -/

namespace MallikDegree

variable {α : Type*} [Fintype α]

theorem residual_hall {R : α → α → Prop} {k : ℕ} (expands : Expands R k)
    (u v : Fin k ↪ α) :
    ∃ f : {x : α // x∉occupied u} ≃ {x : α // x∉occupied v},∀ (a : {x : α // x∉occupied u}),R a.val (f a).val := by
  classical
  let A := occupied u
  let B := occupied v
  let left := Function.Embedding.subtype (fun x : α => x∉A)
  let right := Function.Embedding.subtype (fun x : α => x∉B)
  let rel (x : {a : α // a∉A}) (y : {a : α // a∉B}) := R x.val y.val
  have hall (X : Finset {a : α // a∉A}) :
      X.card≤(Finset.univ.filter fun y => ∃ x∈X,rel x y).card := by
    by_cases nonempty : X.Nonempty
    · let Z := X.map left
      have rem : Z⊆Finset.univ \ A := by
        intro a mem
        obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp mem
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,x.property⟩
      have size := Finset.card_le_card rem
      have total := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
      have bounded : Z.card+k≤Fintype.card α := by
        have countA : A.card=k := occupied_card u
        rw [countA,Finset.card_univ] at total
        omega
      have wide := expands Z nonempty.map bounded
      let Y := Finset.univ.filter fun y => ∃ x∈X,rel x y
      have eq : (neighbors R Z) \ B=Y.map right := by
        ext y
        simp only [Finset.mem_sdiff,mem_neighbors,Finset.mem_map]
        constructor
        · rintro ⟨⟨x,hx,edge⟩,hy⟩
          obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
          exact ⟨⟨y,hy⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,ha,edge⟩,rfl⟩
        · rintro ⟨b,hb,rfl⟩
          obtain ⟨a,ha,edge⟩ := (Finset.mem_filter.mp hb).2
          exact ⟨⟨a.val,Finset.mem_map.mpr ⟨a,ha,rfl⟩,edge⟩,b.property⟩
      have outside := Finset.card_le_card_sdiff_add_card (s := neighbors R Z) (t := B)
      rw [eq,Finset.card_map,occupied_card v] at outside
      change X.card≤Y.card
      have zcard : Z.card=X.card := Finset.card_map _
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp nonempty]
  obtain ⟨f,inj,edges⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hall
  have same : Fintype.card {x : α // x∉A}=Fintype.card {x : α // x∉B} := by
    simp only [Fintype.card_subtype_compl,Fintype.card_coe,A,B,occupied_card]
  let g := Equiv.ofBijective f ⟨inj,inj.surjective_of_finite (Fintype.equivOfCardEq same)⟩
  exact ⟨g,edges⟩

theorem extends_of_expansion {R : α → α → Prop} {k : ℕ} (expands : Expands R k) : Extends R k := by
  classical
  intro u v edge
  obtain ⟨g,remaining⟩ := residual_hall expands u v
  let assigned := (indexEquiv u).symm.trans (indexEquiv v)
  let f := (Equiv.sumCompl (fun x : α => x∈occupied u)).symm.trans
    ((assigned.sumCongr g).trans (Equiv.sumCompl (fun x : α => x∈occupied v)))
  have fixed (i : Fin k) : f (u i)=v i := by
    have mem := mem_occupied u i
    have tagged : (⟨u i,mem⟩ : occupied u)=indexEquiv u i := rfl
    simp only [f,Equiv.trans_apply,Equiv.sumCompl_symm_apply_of_pos mem,Equiv.sumCongr_apply,Sum.map_inl,
      Equiv.sumCompl_apply_inl,tagged,assigned,Equiv.symm_apply_apply,indexEquiv_val]
  refine ⟨f,?_,fixed⟩
  intro x
  by_cases hx : x∈occupied u
  · obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    rw [fixed]
    exact edge i
  · simpa only [f,Equiv.trans_apply,Equiv.sumCompl_symm_apply_of_neg hx,Equiv.sumCongr_apply,
      Sum.map_inr,Equiv.sumCompl_apply_inr] using remaining ⟨x,hx⟩

end MallikDegree
