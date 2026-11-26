import Conjectures.SteinerSailSystem
import Mathlib.Algebra.Order.Chebyshev

/-! Double-counting the colored incidences gives the degree sums, the total
number of blocks, and the variance bound used in the sail proof. -/

namespace SteinerSail

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem sum_incident_cards (A : Finset (Finset V)) :
    (∑ x : V,(A.filter fun T => x∈T).card)=∑ T∈A,T.card := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  simp

namespace System

def blocksOf (S : System V) (color : Finset V → Bool) (c : Bool) : Finset (Finset V) :=
  S.blocks.filter fun T => color T=c

noncomputable def degree (S : System V) (color : Finset V → Bool) (x : V) (c : Bool) : ℕ :=
  (S.neighbors color x c).card

omit [Fintype V] in
theorem through_incident (S : System V) (color : Finset V → Bool) (x : V) (c : Bool) :
    S.through color x c=(S.blocksOf color c).filter fun T => x∈T := by
  ext T; simp [through,blocksOf,and_assoc,and_comm,and_left_comm]

theorem neighbor_colors_disjoint (S : System V) (color : Finset V → Bool) (x : V) : Disjoint (S.neighbors color x true) (S.neighbors color x false) := by
  apply Finset.disjoint_left.mpr
  intro y hr hb
  exact Bool.noConfusion (((Finset.mem_filter.mp hr).2.2).symm.trans ((Finset.mem_filter.mp hb).2.2))

theorem neighbor_colors_union (S : System V) (color : Finset V → Bool) (x : V) : S.neighbors color x true∪S.neighbors color x false=Finset.univ.erase x := by
  ext y
  simp only [neighbors,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,and_true]
  cases color (S.join x y) <;> simp [ne_comm]

theorem degree_sum_point (S : System V) (color : Finset V → Bool) (x : V) :
    S.degree color x true+S.degree color x false=Fintype.card V-1 := by
  rw [degree,degree,←Finset.card_union_of_disjoint (S.neighbor_colors_disjoint color x),S.neighbor_colors_union,Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]

theorem degree_sum_color (S : System V) (color : Finset V → Bool) (c : Bool) :
    (∑ x : V,S.degree color x c)=6*(S.blocksOf color c).card := by
  simp only [degree,neighbor_degree,through_incident,←Finset.mul_sum,sum_incident_cards]
  have triple (T) (hT : T∈S.blocksOf color c) : T.card=3 := S.triple _ (Finset.mem_filter.mp hT).1
  rw [Finset.sum_congr rfl triple]
  simp
  ring

theorem block_count (S : System V) (color : Finset V → Bool) :
    6*((S.blocksOf color true).card+(S.blocksOf color false).card)=Fintype.card V*(Fintype.card V-1) := by
  rw [Nat.mul_add,←S.degree_sum_color color true,←S.degree_sum_color color false,←Finset.sum_add_distrib]
  simp [degree_sum_point]

noncomputable def variance (S : System V) (color : Finset V → Bool) : ℝ :=
  ∑ x : V,((S.degree color x true : ℝ)-(S.degree color x false : ℝ))^2

theorem variance_nonneg (S : System V) (color : Finset V → Bool) : 0≤S.variance color :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem degree_spread (S : System V) (color : Finset V → Bool) :
    36*(((S.blocksOf color true).card : ℝ)-((S.blocksOf color false).card : ℝ))^2 ≤
      (Fintype.card V : ℝ)*S.variance color := by
  let d (x : V) : ℝ := (S.degree color x true : ℝ)-(S.degree color x false : ℝ)
  have realSum (c : Bool) : (∑ x : V,(S.degree color x c : ℝ))=6*((S.blocksOf color c).card : ℝ) := by
    exact_mod_cast S.degree_sum_color color c
  have sub : (∑ x : V,d x)=6*(((S.blocksOf color true).card : ℝ)-((S.blocksOf color false).card : ℝ)) := by
    simp only [d,Finset.sum_sub_distrib,realSum,mul_sub]
  have bound := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V)) (f := d)
  rw [sub,Finset.card_univ,mul_pow] at bound
  norm_num at bound
  simpa only [variance,d] using bound

end System
end SteinerSail
