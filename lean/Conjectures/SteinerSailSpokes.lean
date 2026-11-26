import Conjectures.SteinerSailMixed

/-! Double-count the agreeing incidences and remove incident centers. -/

namespace SteinerSail.System

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem all_spokes (S : System V) (color : Finset V → Bool) :
    (∑ p : V,∑ T∈S.blocks,S.spokes color p T)=
      ∑ x : V,(S.degree color x true*(S.through color x true).card+
        S.degree color x false*(S.through color x false).card) := by
  let score (p x : V) (T : Finset V) : ℕ :=
    if x∈T ∧ x≠p ∧ color (S.join p x)=color T then 1 else 0
  have expand (p : V) (T : Finset V) : S.spokes color p T=∑ x : V,score p x T := by
    simp only [score,Finset.sum_boole,Nat.cast_id,spokes]
    congr 1
    ext x
    simp
  have centers (x : V) (T : Finset V) :
      (∑ p : V,score p x T)=if x∈T then S.degree color x (color T) else 0 := by
    by_cases hx : x∈T
    · simp only [hx,ite_true,score,true_and,Finset.sum_boole,Nat.cast_id,degree,neighbors]
      congr 1
      ext p
      simp [S.join_comm p x]
    · simp [score,hx]
  have colored (x : V) :
      (∑ T∈S.blocks,if x∈T then S.degree color x (color T) else 0)=
        S.degree color x true*(S.through color x true).card+
        S.degree color x false*(S.through color x false).card := by
    simp only [through,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hx : x∈T <;> cases color T <;> simp [hx]
  simp only [expand]
  conv_lhs =>
    enter [2,p]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  simp only [centers,colored]

omit [Fintype V] in
theorem all_blocks_card (S : System V) (color : Finset V → Bool) :
    (S.blocksOf color true).card+(S.blocksOf color false).card=S.blocks.card := by
  have cut := Finset.card_filter_add_card_filter_not (s := S.blocks) (p := fun T => color T=true)
  simpa only [blocksOf,Bool.not_eq_true] using cut

theorem outside_spokes (S : System V) (color : Finset V → Bool) :
    S.outsideSum (S.spokes color)+Fintype.card V*(Fintype.card V-1)=
      ∑ p : V,∑ T∈S.blocks,S.spokes color p T := by
  have inc : (∑ p : V,∑ T∈S.blocks,if p∈T then (2 : ℕ) else 0)=6*S.blocks.card := by
    rw [Finset.sum_comm]
    have term (T : Finset V) (ht : T∈S.blocks) : (∑ p : V,if p∈T then (2 : ℕ) else 0)=6 := by
      rw [Finset.sum_ite]
      simp [S.triple _ ht]
    rw [Finset.sum_congr rfl term]
    simp [mul_comm]
  have count := S.block_count color
  rw [S.all_blocks_card] at count
  rw [←count,←inc,outsideSum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T ht
  by_cases hp : p∈T
  · simp [hp,S.incident_spokes color ht hp]
  · simp [hp]

theorem twice_spokes (S : System V) (color : Finset V → Bool) :
    2*(S.outsideSum (S.spokes color)+Fintype.card V*(Fintype.card V-1))=
      ∑ x : V,(S.degree color x true^2+S.degree color x false^2) := by
  rw [S.outside_spokes,S.all_spokes,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have red : S.degree color x true=2*(S.through color x true).card := S.neighbor_degree color x true
  have blue : S.degree color x false=2*(S.through color x false).card := S.neighbor_degree color x false
  rw [red,blue]
  ring

theorem odd_count (S : System V) (color : Finset V → Bool) (hn : 1≤Fintype.card V) :
    2*(S.frequency color 1 : ℝ)=6*(S.frequency color 3 : ℝ)+
      2*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)-S.variance color := by
  have mix : (S.outsideSum (S.spokes color) : ℝ)+(S.frequency color 1 : ℝ)=
      (∑ x : V,(S.degree color x true : ℝ)*(S.degree color x false : ℝ))+3*(S.frequency color 3 : ℝ) := by
    exact_mod_cast S.mixed_spoke_count color
  have twice : 2*((S.outsideSum (S.spokes color) : ℝ)+(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1))=
      ∑ x : V,((S.degree color x true : ℝ)^2+(S.degree color x false : ℝ)^2) := by
    have eq := congrArg (fun n : ℕ => (n : ℝ)) (S.twice_spokes color)
    push_cast [Nat.cast_sub hn] at eq
    exact eq
  have spread : S.variance color=(∑ x : V,((S.degree color x true : ℝ)^2+(S.degree color x false : ℝ)^2))-
      2*∑ x : V,(S.degree color x true : ℝ)*(S.degree color x false : ℝ) := by
    rw [variance,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  linarith only [mix,twice,spread]

end SteinerSail.System
