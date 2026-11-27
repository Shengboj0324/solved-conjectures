import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-! Weak compositions as actual arrays of nonnegative integers, with a slack
coordinate for an inequality on their total. -/

namespace TransportationEhrhart

abbrev Row (α : Type*) [Fintype α] (k : ℕ) := {v : α → ℕ // ∑ i,v i=k}
abbrev AtMost (α : Type*) [Fintype α] (k : ℕ) := {v : α → ℕ // ∑ i,v i≤k}

instance rowFinite (α : Type*) [Fintype α] (k : ℕ) : Finite (Row α k) :=
  by classical exact Finite.of_equiv _ (Sym.equivNatSumOfFintype α k)

theorem row_card (α : Type*) [Fintype α] (k : ℕ) :
    Nat.card (Row α k) = (Fintype.card α+k-1).choose k := by
  classical
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype α k), Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]

def withSlack {α : Type*} [Fintype α] (k : ℕ) : AtMost α k ≃ Row (Option α) k where
  toFun v := ⟨fun i => i.elim (k-∑ j,v.val j) v.val,by
    rw [Fintype.sum_option]
    exact Nat.sub_add_cancel v.property⟩
  invFun v := ⟨fun j => v.val (some j),by
    have h := v.property
    rw [Fintype.sum_option] at h
    change (∑ j,v.val (some j)) ≤ k
    omega⟩
  left_inv _ := rfl
  right_inv v := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      have h := v.property
      rw [Fintype.sum_option] at h
      change k - ∑ j,v.val (some j) = v.val none
      omega
    | some => rfl

theorem atMost_card (α : Type*) [Fintype α] (k : ℕ) :
    Nat.card (AtMost α k) = (Fintype.card α+k).choose k := by
  rw [Nat.card_congr (withSlack k),row_card,Fintype.card_option]
  congr 1
  omega

theorem entry_le {α : Type*} [Fintype α] {k : ℕ} (v : Row α k) (i : α) : v.val i ≤ k := by
  exact (Finset.single_le_sum (f := v.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq v.property

def insertAt {α : Type*} [DecidableEq α] (j : α) (value : ℕ)
    (rest : {x : α // x ≠ j} → ℕ) (i : α) : ℕ :=
  if h : i=j then value else rest ⟨i,h⟩

@[simp] theorem insertAt_self {α : Type*} [DecidableEq α] (j : α) (z : ℕ) (v) :
    insertAt j z v j=z := by simp [insertAt]

@[simp] theorem insertAt_other {α : Type*} [DecidableEq α] (j : α) (z : ℕ)
    (v : {x : α // x≠j} → ℕ) (i : {x : α // x≠j}) : insertAt j z v i=v i := by simp [insertAt, i.property]

theorem sum_away {α : Type*} [Fintype α] [DecidableEq α] (j : α) (f : α → ℕ) :
    ∑ i,f i=f j+∑ i : {x : α // x ≠ j},f i := by
  rw [Fintype.sum_eq_add_sum_compl j]
  congr 1
  exact Finset.sum_subtype _ (by simp) _

theorem sum_insertAt {α : Type*} [Fintype α] [DecidableEq α] (j : α) (z : ℕ) (v) :
    ∑ i,insertAt j z v i=z+∑ i,v i := by
  rw [sum_away j]
  simp

end TransportationEhrhart
