import Conjectures.SteinerSailPackingLemma
import Conjectures.SteinerSailPointCounts

/-! Pack vertex-disjoint monochromatic sails in one common color. -/

namespace SteinerSail.System

variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def colorClass (S : System V) (color : Finset V → Bool) (c : Bool) : Finset (V × Finset V) :=
  (S.outside.filter fun q => S.spokes color q.1 q.2=3).filter fun q => color q.2=c

theorem class_spec (S : System V) (color : Finset V → Bool) {c : Bool} {q : V × Finset V}
    (h : q∈S.colorClass color c) : q.2∈S.blocks ∧ q.1∉q.2 ∧ ∀ U∈S.sailBlocks q.1 q.2,color U=c := by
  obtain ⟨h,co⟩ := Finset.mem_filter.mp h
  obtain ⟨o,three⟩ := Finset.mem_filter.mp h
  obtain ⟨pair,outside⟩ := Finset.mem_filter.mp o
  have block := (Finset.mem_product.mp pair).2
  exact ⟨block,outside,fun U hu => ((S.spokes_three_iff color block outside).mp three U hu).trans co⟩

theorem largest_class (S : System V) (color : Finset V → Bool) :
    ∃ c : Bool,S.frequency color 3≤2*(S.colorClass color c).card := by
  have split := Finset.card_filter_add_card_filter_not
    (s := S.outside.filter fun q => S.spokes color q.1 q.2=3) (p := fun q => color q.2=true)
  simp only [Bool.not_eq_true] at split
  change (S.colorClass color true).card+(S.colorClass color false).card=S.frequency color 3 at split
  by_cases h : (S.colorClass color true).card≤(S.colorClass color false).card
  · exact ⟨false,by omega⟩
  · exact ⟨true,by omega⟩

theorem monochromatic_packing (S : System V) (color : Finset V → Bool) (hn : 3≤Fintype.card V) :
    ∃ (c : Bool) (M : Finset (V × Finset V)), M⊆S.colorClass color c ∧
      (M : Set (V × Finset V)).Pairwise (fun a b => Disjoint (S.vertices a.1 a.2) (S.vertices b.1 b.2)) ∧
      3*S.frequency color 3≤49*(Fintype.card V-1)*(Fintype.card V-3)*M.card := by
  obtain ⟨c,large⟩ := S.largest_class color
  let A := S.colorClass color c
  let support (q : V × Finset V) := S.vertices q.1 q.2
  have size (q) (hq : q∈A) : (support q).card=7 := by
    obtain ⟨block,out,_⟩ := S.class_spec color hq
    exact S.vertices_card block out
  have cap (v : V) : 6*(A.filter fun q => v∈support q).card≤7*(Fintype.card V-1)*(Fintype.card V-3) := by
    have sub : A.filter (fun q => v∈support q) ⊆ S.outside.filter (fun q => v∈support q) := by
      intro q h
      obtain ⟨hq,incl⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1,incl⟩
    exact (Nat.mul_le_mul_left 6 (Finset.card_le_card sub)).trans_eq (S.point_incidence v hn)
  obtain ⟨M,sub,pairs,number⟩ := finite_packing A support _ size cap
  refine ⟨c,M,sub,pairs,?_⟩
  change S.frequency color 3≤2*A.card at large
  have lo : 3*S.frequency color 3≤6*A.card := by omega
  exact (lo.trans number).trans_eq (by ring)

theorem linear_packing (S : System V) (color : Finset V → Bool) (hn : 5≤Fintype.card V) :
    ∃ (c : Bool) (M : Finset (V × Finset V)), M⊆S.colorClass color c ∧
      (M : Set (V × Finset V)).Pairwise (fun a b => Disjoint (S.vertices a.1 a.2) (S.vertices b.1 b.2)) ∧
      (Fintype.card V : ℝ)-196≤4802*(M.card : ℝ) := by
  obtain ⟨c,M,sub,dis,packing⟩ := S.monochromatic_packing color (by omega)
  refine ⟨c,M,sub,dis,?_⟩
  let n : ℝ := Fintype.card V
  have high : 5≤n := by unfold n; exact_mod_cast hn
  have total := congrArg (fun k : ℕ => (k : ℝ)) S.total_sails
  push_cast [Nat.cast_sub (by omega : 1≤Fintype.card V),Nat.cast_sub (by omega : 3≤Fintype.card V)] at total
  change 6*(S.outside.card : ℝ)=n*(n-1)*(n-3) at total
  have dens := S.density_bound color hn
  change (n-196)*(S.outside.card : ℝ)≤49*n*(S.frequency color 3 : ℝ) at dens
  have upper := (Nat.cast_le (α := ℝ)).mpr packing
  push_cast [Nat.cast_sub (by omega : 1≤Fintype.card V),Nat.cast_sub (by omega : 3≤Fintype.card V)] at upper
  change 3*(S.frequency color 3 : ℝ)≤49*(n-1)*(n-3)*(M.card : ℝ) at upper
  have pos : 0<n*(n-1)*(n-3) := mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  apply le_of_mul_le_mul_right (a := n*(n-1)*(n-3)) _ pos
  have counted := congrArg (fun x : ℝ => (n-196)*x) total
  have packed := mul_le_mul_of_nonneg_left upper (show 0≤98*n by linarith)
  nlinarith only [dens,counted,packed]

end SteinerSail.System
