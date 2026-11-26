import Conjectures.MallikDegreeFamily
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Degrees, edge counts and the literal proposed inequality. -/

namespace MallikDegree

noncomputable def degree {α : Type*} [Fintype α] (R : α → α → Prop) (x : α) : ℕ :=
  (neighbors R {x}).card

noncomputable def edges {α : Type*} [Fintype α] (R : α → α → Prop) : ℕ := ∑ x,degree R x

noncomputable def degreeCount {α : Type*} [Fintype α] (R : α → α → Prop) (d : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun x => degree R x=d).card+
    (Finset.univ.filter fun y => degree (fun x z => R z x) y=d).card

variable {H L : Type*} [DecidableEq H] [Fintype H] [Fintype L]

theorem high_degree (D : Finset H) (h : H) :
    degree (family (L := L) D) (.inl h)=Fintype.card L+(if h∈D then 1 else 0) := by
  classical
  rw [degree,family_neighbors,Finset.card_disjSum]
  have sl : ({Sum.inl h} : Finset (H ⊕ L)).toLeft={h} := by ext; simp
  have sr : ({Sum.inl h} : Finset (H ⊕ L)).toRight=∅ := by ext; simp
  by_cases hd : h∈D <;> simp [sl,sr,hd,add_comm]

theorem low_degree (D : Finset H) (l : L) :
    degree (family D) (.inr l)=Fintype.card H+1 := by
  classical
  rw [degree,family_neighbors,Finset.card_disjSum]
  have sl : ({Sum.inr l} : Finset (H ⊕ L)).toLeft=∅ := by ext; simp
  have sr : ({Sum.inr l} : Finset (H ⊕ L)).toRight={l} := by ext; simp
  simp [sl,sr]

theorem family_edges (D : Finset H) :
    edges (family (L := L) D)=2*Fintype.card H*Fintype.card L+Fintype.card L+D.card := by
  classical
  rw [edges,Fintype.sum_sum_type]
  simp only [high_degree,low_degree,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Nat.cast_id,Finset.sum_boole]
  simp
  ring

theorem family_degree_count (D : Finset H) (gap : Fintype.card H+2≤Fintype.card L) :
    degreeCount (family (L := L) D) (Fintype.card H+1)=2*Fintype.card L := by
  classical
  have sym : (fun (x y : H ⊕ L) => family D y x)=family D := by
    funext x y
    exact propext (family_symm D y x)
  have eq : (Finset.univ.filter fun x : H ⊕ L => degree (family D) x=Fintype.card H+1)=
      (Finset.univ : Finset L).map Function.Embedding.inr := by
    ext x
    cases x with
    | inl h =>
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,high_degree,Finset.mem_map,
        Function.Embedding.inr_apply,reduceCtorEq,and_false,exists_false,iff_false]
      split <;> omega
    | inr l => simp [low_degree]
  rw [degreeCount,sym,eq,Finset.card_map,Finset.card_univ]
  omega

theorem strict_deficit {k t r : ℕ} (hk : 3≤k) (hu : t≤2*k-1) (hr : r=2*k-t) :
    (2*t : ℝ)<2*((2*(k : ℝ)*t+t+r)-2*((k : ℝ)+t)+2*k)/(2*k-1) := by
  have hk' : 3≤(k : ℝ) := by exact_mod_cast hk
  have hr' : 0<(r : ℝ) := by exact_mod_cast (by omega : 0<r)
  apply (lt_div_iff₀ (by linarith : 0<2*(k : ℝ)-1)).mpr
  nlinarith only [hr']

end MallikDegree
