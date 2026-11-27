import Conjectures.SteinerSailPacking
import Conjectures.SteinerSailShape

/-! The original two-color Ramsey question, its density estimate, and the
one-color linear packing and fixed disjoint-union consequences. -/

namespace SteinerSail.System

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

theorem actual_sail_from_84 (S : System V) (color : Finset V → Bool) (hn : 84≤Fintype.card V) :
    ∃ (p : V) (T : Finset V), T∈S.blocks ∧ p∉T ∧ (S.sailBlocks p T).card=4 ∧
      (S.vertices p T).card=7 ∧ ∀ U∈S.sailBlocks p T,U∈S.blocks ∧ color U=color T := by
  obtain ⟨p,T,ht,hp,three⟩ := S.exists_monochromatic color hn
  refine ⟨p,T,ht,hp,S.sail_blocks_card ht hp,S.vertices_card ht hp,?_⟩
  intro U hU
  refine ⟨?_,(S.spokes_three_iff color ht hp).mp three U hU⟩
  rcases Finset.mem_insert.mp hU with rfl|spoke
  · exact ht
  · exact (S.spoke_block_spec hp spoke).1

theorem density_fraction (S : System V) (color : Finset V → Bool) (hn : 5≤Fintype.card V) :
    1/49-(4 : ℝ)/(Fintype.card V : ℝ) ≤ (S.frequency color 3 : ℝ)/S.outside.card := by
  let n : ℝ := Fintype.card V
  have high : 5≤n := by unfold n; exact_mod_cast hn
  have npos : 0<n := by linarith
  have total := congrArg (fun k : ℕ => (k : ℝ)) S.total_sails
  push_cast [Nat.cast_sub (by omega : 1≤Fintype.card V),Nat.cast_sub (by omega : 3≤Fintype.card V)] at total
  change 6*(S.outside.card : ℝ)=n*(n-1)*(n-3) at total
  have positive : 0<(S.outside.card : ℝ) := by
    have right : 0<n*(n-1)*(n-3) := mul_pos (mul_pos npos (by linarith)) (by linarith)
    linarith
  have bound := S.density_bound color hn
  change (n-196)*(S.outside.card : ℝ)≤49*n*(S.frequency color 3 : ℝ) at bound
  change 1/49-4/n≤(S.frequency color 3 : ℝ)/S.outside.card
  apply (le_div_iff₀ positive).mpr
  apply (mul_le_mul_iff_of_pos_right npos).mp
  field_simp [ne_of_gt npos]
  nlinarith only [bound]

theorem eventually_density (ε : ℝ) (pos : 0<ε) : ∃ N : ℕ, ∀ {W : Type u} [DecidableEq W] [Fintype W]
    (S : System W) (color : Finset W → Bool), N≤Fintype.card W →
      1/49-ε≤(S.frequency color 3 : ℝ)/S.outside.card := by
  obtain ⟨m,hm⟩ := exists_nat_gt (4/ε)
  refine ⟨max 5 m,?_⟩
  intro W _ _ S color hn
  obtain ⟨order,large⟩ := max_le_iff.mp hn
  have posN : 0<(Fintype.card W : ℝ) := by exact_mod_cast (by omega : 0<Fintype.card W)
  have big : (m : ℝ)≤Fintype.card W := by exact_mod_cast large
  have small : 4/(Fintype.card W : ℝ)≤ε := (div_le_iff₀ posN).mpr (by
    have prod := (div_lt_iff₀ pos).mp (hm.trans_le big)
    linarith)
  exact (sub_le_sub_left small _).trans (S.density_fraction color order)

theorem fixed_disjoint_union (S : System V) (color : Finset V → Bool) (k : ℕ)
    (hn : 4802*k+196≤Fintype.card V) :
    ∃ (c : Bool) (M : Finset (V × Finset V)), M.card=k ∧ M⊆S.colorClass color c ∧
      (M : Set (V × Finset V)).Pairwise (fun a b => Disjoint (S.vertices a.1 a.2) (S.vertices b.1 b.2)) := by
  obtain ⟨c,A,sub,dis,lower⟩ := S.linear_packing color (by omega)
  have realn : 4802*(k : ℝ)+196≤(Fintype.card V : ℝ) := by exact_mod_cast hn
  have hk : k≤A.card := by exact_mod_cast (by linarith : (k : ℝ)≤(A.card : ℝ))
  obtain ⟨M,inside,count⟩ := Finset.exists_subset_card_eq hk
  exact ⟨c,M,count,inside.trans sub,dis.mono inside⟩

theorem eventually_packing (ε : ℝ) (pos : 0<ε) : ∃ N : ℕ, ∀ {W : Type u} [DecidableEq W] [Fintype W]
    (S : System W) (color : Finset W → Bool), N≤Fintype.card W →
      ∃ (c : Bool) (M : Finset (W × Finset W)), M⊆S.colorClass color c ∧
        (M : Set (W × Finset W)).Pairwise (fun a b => Disjoint (S.vertices a.1 a.2) (S.vertices b.1 b.2)) ∧
        (1/4802-ε)*(Fintype.card W : ℝ)≤M.card := by
  obtain ⟨m,hm⟩ := exists_nat_gt (1/ε)
  refine ⟨max 5 m,?_⟩
  intro W _ _ S color hn
  obtain ⟨order,large⟩ := max_le_iff.mp hn
  obtain ⟨c,M,sub,dis,lower⟩ := S.linear_packing color order
  have big : (m : ℝ)≤Fintype.card W := by exact_mod_cast large
  have stop := (div_lt_iff₀ pos).mp (hm.trans_le big)
  exact ⟨c,M,sub,dis,by nlinarith only [lower,stop]⟩

end SteinerSail.System
