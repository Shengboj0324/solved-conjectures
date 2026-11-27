import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

/-! Two real-root counting lemmas for sign certificates. -/

namespace TransportationEhrhart

open Polynomial

theorem nonsplit_loses_two {p : ℝ[X]} (h : ¬p.Splits) : p.roots.card+2 ≤ p.natDegree := by
  classical
  have hp : p ≠ 0 := fun hp => h (hp ▸ Splits.zero)
  obtain ⟨q,fac⟩ := prod_multiset_X_sub_C_dvd p
  have nz : (p.roots.map (fun a => X-C a)).prod*q ≠ 0 := fac ▸ hp
  have deg := congrArg natDegree fac
  rw [natDegree_mul (left_ne_zero_of_mul nz) (right_ne_zero_of_mul nz),
    natDegree_multiset_prod_X_sub_C_eq_card] at deg
  have nonsmall : ¬q.natDegree ≤ 1 := by
    intro small
    apply h
    rw [fac]
    apply Splits.mul _ (Splits.of_natDegree_le_one small)
    apply Splits.multisetProd
    intro f hf
    obtain ⟨a,_,rfl⟩ := Multiset.mem_map.mp hf
    exact Splits.X_sub_C a
  omega

theorem root_in_sign_interval {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (signs : p.eval a * p.eval b < 0) : ∃ x ∈ Set.Ioo a b, p.eval x=0 := by
  rcases mul_neg_iff.mp signs with ⟨ha,hb⟩|⟨ha,hb⟩
  · exact intermediate_value_Ioo' hab.le p.continuous.continuousOn ⟨hb,ha⟩
  · exact intermediate_value_Ioo hab.le p.continuous.continuousOn ⟨ha,hb⟩

theorem count_sign_intervals {d : ℕ} {p : ℝ[X]} (hp : p ≠ 0) (a : Fin (d+1) → ℝ)
    (mono : StrictMono a) (flip : ∀ i : Fin d,p.eval (a i.castSucc) * p.eval (a i.succ) < 0) :
    d ≤ p.roots.toFinset.card := by
  classical
  have hex (i : Fin d) := root_in_sign_interval (mono (show i.castSucc < i.succ from Fin.castSucc_lt_succ)) (flip i)
  choose w between root using hex
  have increasing : StrictMono w := by
    intro i j lt
    have order : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; omega
    exact lt_trans ((between i).2.trans_le (mono.monotone order)) (between j).1
  let emb : Fin d → ↥p.roots.toFinset := fun i =>
    ⟨w i,Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (root i))⟩
  have inject : Function.Injective emb := fun _ _ eq => increasing.injective (congrArg Subtype.val eq)
  simpa using Fintype.card_le_of_injective emb inject

end TransportationEhrhart
