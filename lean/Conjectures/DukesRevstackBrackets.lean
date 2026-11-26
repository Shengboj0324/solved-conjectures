import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-! Alternating disjoint intervals certify all roots and their multiplicities
for two real monic polynomials of consecutive degrees. -/

open Polynomial

namespace DukesRevstack

private theorem root_in_interval (p : ℝ[X]) {l r : ℝ} (lr : l<r)
    (sign : p.eval l*p.eval r<0) : ∃ x ∈ Set.Ioo l r,p.eval x=0 := by
  rcases mul_neg_iff.mp sign with ⟨left,right⟩ | ⟨left,right⟩
  · exact intermediate_value_Ioo' lr.le p.continuous.continuousOn ⟨right,left⟩
  · exact intermediate_value_Ioo lr.le p.continuous.continuousOn ⟨left,right⟩

private theorem roots_in_brackets {d : ℕ} (p : ℝ[X]) (hp : IsMonicOfDegree p d)
    (lo hi : Fin d → ℝ) (proper : ∀ i,lo i<hi i)
    (separated : ∀ i j : Fin d,i<j → hi i≤lo j)
    (sign : ∀ i,p.eval (lo i)*p.eval (hi i)<0) :
    ∃ a : Fin d → ℝ,(∀ i,a i∈Set.Ioo (lo i) (hi i)) ∧ StrictMono a ∧
      p=(∏ i : Fin d, (X - C (a i))) := by
  classical
  choose a interval root using fun i => root_in_interval p (proper i) (sign i)
  have ordered : StrictMono a := fun i j hij =>
    (interval i).2.trans_le ((separated i j hij).trans (interval j).1.le)
  let points := Finset.univ.image a
  have card : points.card=d := by simp [points,Finset.card_image_of_injective _ ordered.injective]
  have roots : p.roots=points.val := roots_eq_of_natDegree_le_card_of_ne_zero
    (by intro x hx; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx; exact root i)
    (by rw [card,hp.natDegree_eq]) hp.monic.ne_zero
  have full : p.roots.card=p.natDegree := by rw [roots]; simpa [hp.natDegree_eq] using card
  refine ⟨a,interval,ordered,?_⟩
  rw [←prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp.monic full,roots]
  change (∏ x ∈ points,(X-C x))=_
  exact Finset.prod_image ordered.injective.injOn

theorem interlacing_of_cuts {d : ℕ} (p q : ℝ[X]) (hp : IsMonicOfDegree p d)
    (hq : IsMonicOfDegree q (d+1)) (c : ℕ → ℝ)
    (inc : ∀ i j,i<j → j≤2*d+1 → c i<c j) (last : c (2*d+1)≤0)
    (oldSigns : ∀ i : Fin d,p.eval (c (2*i.val+1))*p.eval (c (2*i.val+2))<0)
    (newSigns : ∀ i : Fin (d+1),q.eval (c (2*i.val))*q.eval (c (2*i.val+1))<0) :
    ∃ a : Fin d → ℝ,∃ b : Fin (d+1) → ℝ,
      StrictMono a ∧ StrictMono b ∧ (∀ i,a i<0) ∧ (∀ i,b i<0) ∧
      (∀ i : Fin d,b i.castSucc<a i ∧ a i<b i.succ) ∧
      p=(∏ i : Fin d, (X - C (a i))) ∧ q=(∏ i : Fin (d+1), (X - C (b i))) := by
  have weak {i j : ℕ} (le : i≤j) (endp : j≤2*d+1) : c i≤c j := by
    rcases le.eq_or_lt with eq|lt
    · rw [eq]
    · exact (inc _ _ lt endp).le
  obtain ⟨a,ia,ma,fa⟩ := roots_in_brackets p hp
    (fun i => c (2*i.val+1)) (fun i => c (2*i.val+2))
    (fun i => inc _ _ (by omega) (by omega))
    (fun i j smaller => weak (by omega) (by omega)) oldSigns
  obtain ⟨b,ib,mb,fb⟩ := roots_in_brackets q hq
    (fun i => c (2*i.val)) (fun i => c (2*i.val+1))
    (fun i => inc _ _ (by omega) (by omega))
    (fun i j smaller => weak (by omega) (by omega)) newSigns
  refine ⟨a,b,ma,mb,fun i => (ia i).2.trans_le ((weak (by omega) le_rfl).trans last),
    fun i => (ib i).2.trans_le ((weak (by omega) le_rfl).trans last),fun i => ?_,fa,fb⟩
  refine ⟨(ib i.castSucc).2.trans (ia i).1,?_⟩
  have align : 2*i.val+2=2*i.succ.val := by simp; omega
  exact (ia i).2.trans (align ▸ (ib i.succ).1)

end DukesRevstack
