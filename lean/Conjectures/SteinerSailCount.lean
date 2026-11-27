import Conjectures.SteinerSailSpokes
import Conjectures.SteinerSailCover

/-! The uniform lower bound for actual monochromatic sails in every
red--blue coloring of every finite Steiner triple system. -/

namespace SteinerSail.System

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem monochromatic_bound (S : System V) (color : Finset V → Bool) (hn : 1≤Fintype.card V) :
    (Fintype.card V : ℝ)*(Fintype.card V-1)*
      ((Fintype.card V : ℝ)*(Fintype.card V-3)-81*(Fintype.card V-1)) ≤
      (294*(Fintype.card V : ℝ)-288)*(S.frequency color 3 : ℝ) := by
  have opp := (Nat.cast_le (α := ℝ)).mpr (S.opposite_count color)
  have blocks := congrArg (fun i : ℕ => (i : ℝ)) (S.block_count color)
  push_cast [Nat.cast_sub hn] at opp blocks
  exact sail_bound_of_counts (by exact_mod_cast hn) (Nat.cast_nonneg _) (S.variance_nonneg color)
    (S.odd_count color hn) opp blocks (S.degree_spread color)

theorem exists_monochromatic (S : System V) (color : Finset V → Bool) (hn : 84≤Fintype.card V) :
    ∃ p : V,∃ T∈S.blocks,p∉T ∧ S.spokes color p T=3 := by
  have positive := positive_from_84 (by exact_mod_cast hn) (S.monochromatic_bound color (by omega))
  have card : 0<S.frequency color 3 := by exact_mod_cast positive
  obtain ⟨q,hq⟩ := Finset.card_pos.mp card
  obtain ⟨out,hj⟩ := Finset.mem_filter.mp hq
  obtain ⟨pair,hp⟩ := Finset.mem_filter.mp out
  exact ⟨q.1,q.2,(Finset.mem_product.mp pair).2,hp,hj⟩

theorem outside_card (S : System V) :
    S.outside.card=S.blocks.card*(Fintype.card V-3) := by
  simp only [outside,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
  rw [Finset.sum_comm]
  have term (T : Finset V) (ht : T∈S.blocks) :
      (∑ p : V,if p∉T then (1 : ℕ) else 0)=Fintype.card V-3 := by
    rw [Finset.sum_boole]
    have eq : (Finset.univ.filter fun p => p∉T)=Finset.univ \ T := by
      ext p
      simp
    simp [eq,Finset.card_sdiff,S.triple _ ht]
  rw [Finset.sum_congr rfl term]
  simp

theorem total_sails (S : System V) :
    6*S.outside.card=Fintype.card V*(Fintype.card V-1)*(Fintype.card V-3) := by
  have blocks := S.block_count (fun _ => true)
  rw [S.all_blocks_card] at blocks
  rw [S.outside_card,←Nat.mul_assoc,blocks]

theorem density_bound (S : System V) (color : Finset V → Bool) (hn : 5≤Fintype.card V) :
    ((Fintype.card V : ℝ)-196)*(S.outside.card : ℝ)≤
      49*(Fintype.card V : ℝ)*(S.frequency color 3 : ℝ) := by
  let n : ℝ := Fintype.card V
  have high : 5≤n := by unfold n; exact_mod_cast hn
  have total := congrArg (fun i : ℕ => (i : ℝ)) S.total_sails
  push_cast [Nat.cast_sub (by omega : 1≤Fintype.card V),Nat.cast_sub (by omega : 3≤Fintype.card V)] at total
  change 6*(S.outside.card : ℝ)=n*(n-1)*(n-3) at total
  have raw := S.monochromatic_bound color (by omega)
  change n*(n-1)*(n*(n-3)-81*(n-1)) ≤ (294*n-288)*(S.frequency color 3 : ℝ) at raw
  have mul := congrArg (fun x : ℝ => (n-196)*x) total
  have factor : (n-196)*(n-3)≤n*(n-3)-81*(n-1) := by nlinarith only [high]
  have compare := mul_le_mul_of_nonneg_left factor (show 0≤n*(n-1) from mul_nonneg (by linarith) (by linarith))
  change (n-196)*(S.outside.card : ℝ)≤49*n*(S.frequency color 3 : ℝ)
  nlinarith only [raw,mul,compare,Nat.cast_nonneg (α := ℝ) (S.frequency color 3)]

end SteinerSail.System
