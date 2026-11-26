import Conjectures.SteinerSailOpposite

/-! Count red--blue block pairs by a shared vertex or an odd spoke witness. -/

namespace SteinerSail.System

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem opposite_cover (S : System V) (color : Finset V → Bool) :
    (S.blocksOf color true).card*(S.blocksOf color false).card ≤
      (∑ x : V,(S.through color x true).card*(S.through color x false).card)+
      ∑ q∈S.oddPairs color,(S.incident q.1).card := by
  let atPoint (x : V) := S.through color x true ×ˢ S.through color x false
  let certified (q : V × Finset V) := (S.incident q.1).image
    (fun U => if color q.2 then (q.2,U) else (U,q.2))
  have cover : S.blocksOf color true ×ˢ S.blocksOf color false ⊆
      Finset.univ.biUnion atPoint ∪ (S.oddPairs color).biUnion certified := by
    rintro ⟨T,U⟩ pair
    obtain ⟨ht,hu⟩ := Finset.mem_product.mp pair
    obtain ⟨bt,red⟩ := Finset.mem_filter.mp ht
    obtain ⟨bu,blue⟩ := Finset.mem_filter.mp hu
    by_cases dis : Disjoint T U
    · apply Finset.mem_union_right
      rcases S.opposite_witness color bt bu red blue dis with ⟨p,pu,odd⟩|⟨p,pt,odd⟩
      · have out : (p,T)∈S.outside := Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,bt⟩,fun hp => Finset.disjoint_left.mp dis hp pu⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨(p,T),Finset.mem_filter.mpr ⟨out,odd⟩,?_⟩
        exact Finset.mem_image.mpr ⟨U,Finset.mem_filter.mpr ⟨bu,pu⟩,by simp [red]⟩
      · have out : (p,U)∈S.outside := Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,bu⟩,Finset.disjoint_left.mp dis pt⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨(p,U),Finset.mem_filter.mpr ⟨out,odd⟩,?_⟩
        exact Finset.mem_image.mpr ⟨T,Finset.mem_filter.mpr ⟨bt,pt⟩,by simp [blue]⟩
    · obtain ⟨x,xt,xu⟩ := Finset.not_disjoint_iff.mp dis
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨bt,xt,red⟩,Finset.mem_filter.mpr ⟨bu,xu,blue⟩⟩⟩
  have first : (Finset.univ.biUnion atPoint).card ≤
      ∑ x : V,(S.through color x true).card*(S.through color x false).card := by
    simpa only [atPoint,Finset.card_product] using
      (Finset.card_biUnion_le (s := (Finset.univ : Finset V)) (t := atPoint))
  have second : ((S.oddPairs color).biUnion certified).card ≤ ∑ q∈S.oddPairs color,(S.incident q.1).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
  have bound := (Finset.card_le_card cover).trans ((Finset.card_union_le ..).trans (Nat.add_le_add first second))
  simpa only [Finset.card_product] using bound

theorem intersection_bound (S : System V) (color : Finset V → Bool) :
    16*(∑ x : V,(S.through color x true).card*(S.through color x false).card) ≤
      Fintype.card V*(Fintype.card V-1)^2 := by
  rw [Finset.mul_sum]
  have point (x : V) : 16*((S.through color x true).card*(S.through color x false).card) ≤
      (Fintype.card V-1)^2 := by
    have bound := four_mul_le_sq_add (S.degree color x true) (S.degree color x false)
    rw [S.degree_sum_point] at bound
    simp only [degree,neighbor_degree] at bound
    calc
      _ = 4*(2*(S.through color x true).card)*(2*(S.through color x false).card) := by ring
      _ ≤ _ := bound
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset V)) fun x _ => point x

theorem witness_capacity (S : System V) (color : Finset V → Bool) :
    2*(∑ q∈S.oddPairs color,(S.incident q.1).card)=
      (Fintype.card V-1)*(S.frequency color 1+S.frequency color 3) := by
  rw [Finset.mul_sum]
  simp only [S.twice_incident color,Finset.sum_const,nsmul_eq_mul,odd_card]
  exact Nat.mul_comm _ _

theorem opposite_count (S : System V) (color : Finset V → Bool) :
    16*((S.blocksOf color true).card*(S.blocksOf color false).card)≤
      Fintype.card V*(Fintype.card V-1)^2+
      8*(Fintype.card V-1)*(S.frequency color 1+S.frequency color 3) := by
  have ub := Nat.mul_le_mul_left 16 (S.opposite_cover color)
  rw [Nat.mul_add] at ub
  have second := congrArg (fun j : ℕ => 8*j) (S.witness_capacity color)
  simp only [←Nat.mul_assoc] at second
  exact ub.trans (Nat.add_le_add (S.intersection_bound color) (le_of_eq second))

end SteinerSail.System
