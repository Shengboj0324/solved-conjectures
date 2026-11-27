import Conjectures.MonophonicPrismCoverage
import Conjectures.MonophonicPrismColorings

/-! A large color class exhausts a three-edge subdivision star. At most one
such class can meet the three centers of any one of the six port triangles. -/

namespace MonophonicProduct

theorem fiber_is_star {k : ℕ} {col : Vertex → Fin k} (valid : ValidColoring witnessGraph col)
    (color : Fin k) (large : 2<(fiber col color).card) : ∃ s : Fin 18,fiber col color=star s := by
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩:=Finset.two_lt_card_iff.mp large
  have ea:=(mem_fiber ..).1 ha
  have eb:=(mem_fiber ..).1 hb
  have ec:=(mem_fiber ..).1 hc
  obtain ⟨s,sa,sb,_⟩ := monochrome_triple valid ab ac bc (ea.trans eb.symm) (ea.trans ec.symm)
  have subset : fiber col color⊆star s := by
    intro x hx
    by_cases ax : a=x
    · simpa only [←ax] using sa
    by_cases bx : b=x
    · simpa only [←bx] using sb
    have ex:=(mem_fiber ..).1 hx
    obtain ⟨t,ta,tb,tx⟩:=monochrome_triple valid ab ax bx (ea.trans eb.symm) (ea.trans ex.symm)
    by_cases st : s=t
    · simpa only [st] using tx
    exact False.elim (ab (Finset.card_le_one.mp (star_intersections s t st) a
      (Finset.mem_inter.mpr ⟨sa,ta⟩) b (Finset.mem_inter.mpr ⟨sb,tb⟩)))
  exact ⟨s,Finset.eq_of_subset_of_card_le subset (by rw [star_card]; omega)⟩

def largeColors {k : ℕ} (col : Vertex → Fin k) := Finset.univ.filter fun c => 2<(fiber col c).card

theorem large_colors_le_six {k : ℕ} {col : Vertex → Fin k} (valid : ValidColoring witnessGraph col) :
    (largeColors col).card≤6 := by
  classical
  have existsCenter (i : ↥(largeColors col)) : ∃ s : Fin 18,fiber col i.val=star s :=
    fiber_is_star valid i.val (Finset.mem_filter.mp i.property).2
  choose center eq using existsCenter
  let embed (i : ↥(largeColors col)) : Fin 6 := ⟨(center i).val/3,by have := (center i).isLt; omega⟩
  have inj : Function.Injective embed := by
    intro i j e
    obtain ⟨v,vi,vj⟩:=triangle_overlap (center i) (center j) (congrArg Fin.val e)
    rw [←eq] at vi vj
    exact Subtype.ext (((mem_fiber ..).1 vi).symm.trans ((mem_fiber ..).1 vj))
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective embed inj

theorem primal_lower {k : ℕ} {col : Vertex → Fin k} (valid : ValidColoring witnessGraph col) : 20≤k := by
  classical
  let big:=largeColors col
  have each (c : Fin k) : (fiber col c).card≤2+(if c∈big then 1 else 0) := by
    by_cases h : c∈big
    · obtain ⟨s,e⟩:=fiber_is_star valid c (Finset.mem_filter.mp h).2
      rw [e,star_card]
      simp [h]
    · have small : ¬2<(fiber col c).card := by simpa [big,largeColors] using h
      simp [h,le_of_not_gt small]
  have total : 45=∑ c : Fin k,(fiber col c).card := by
    have h:=Finset.card_eq_sum_card_fiberwise (f := col) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    simpa [fiber] using h
  have ex : (∑ c : Fin k,if c∈big then 1 else 0 : ℕ)=big.card := by
    rw [←Finset.sum_filter]
    simp
  have count:=Finset.sum_le_sum (s := Finset.univ) (fun c _ => each c)
  rw [←total,Finset.sum_add_distrib,ex] at count
  simp at count
  have cap:=large_colors_le_six valid
  change big.card≤6 at cap
  omega

theorem primal_exact : ChromaticNumber witnessGraph 20 := ⟨⟨primal,primal_valid⟩,fun _ ⟨_,h⟩ => primal_lower h⟩

theorem monophonic_product_counterexample :
    ∃ G : SimpleGraph Vertex,ChromaticNumber G 20 ∧ ChromaticNumber Gᶜ 27 ∧
      ((Fintype.card Vertex+1 : ℝ)/2)^2<(20 : ℝ)*27 :=
  ⟨witnessGraph,primal_exact,dual_exact,by norm_num [Vertex]⟩

theorem universal_product_false :
    ¬∀ (G : SimpleGraph Vertex) (r s : ℕ),ChromaticNumber G r → ChromaticNumber Gᶜ s →
      4*r*s≤(Fintype.card Vertex+1)^2 := by
  intro h
  have bad:=h witnessGraph 20 27 primal_exact dual_exact
  norm_num [Vertex] at bad

end MonophonicProduct
