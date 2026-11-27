import Conjectures.DukesRevstackDegree
import Conjectures.DukesRevstackHorner
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! A triangular integer recurrence computes the coefficients of the same
Eulerian and revstack polynomials obtained from the actual sorting map. -/

open Polynomial

namespace DukesRevstack

def rowEntry (a : Array ℤ) (k : ℕ) : ℤ := a[k]?.getD 0

private theorem entry_ofFn {d : ℕ} (f : Fin d → ℤ) {k : ℕ} (hk : k<d) :
    rowEntry (Array.ofFn f) k=f ⟨k,hk⟩ := by
  simp [rowEntry,Array.size_ofFn,hk]

private theorem entry_ofFn_out {d : ℕ} (f : Fin d → ℤ) {k : ℕ} (hk : d≤k) :
    rowEntry (Array.ofFn f) k=0 := by
  simp [rowEntry,Array.getElem?_eq_none (by simpa using hk : (Array.ofFn f).size≤k)]

def nextEulerRow (n : ℕ) (a : Array ℤ) : Array ℤ :=
  Array.ofFn fun i : Fin (n+2) => match i.val with
    | 0 => 1
    | k+1 => ((k : ℤ)+2)*rowEntry a (k+1)+((n : ℤ)-k)*rowEntry a k

def eulerRows : ℕ → Array ℤ
  | 0 => #[1]
  | n+1 => nextEulerRow n (eulerRows n)

theorem euler_row_correct (n k : ℕ) :
    (rowEntry (eulerRows n) k : ℝ)=(eulerian (R := ℝ) n).coeff k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [rowEntry,eulerRows]
    | succ k => simp [rowEntry,eulerRows,coeff_one]
  | succ n ih =>
    rw [eulerRows,nextEulerRow]
    by_cases h : k<n+2
    · rw [entry_ofFn _ h]
      cases k with
      | zero => simp [coeff_zero_eq_eval_zero]
      | succ k =>
        rw [eulerian_succ,coeff_eulerianOperator_succ]
        push_cast
        rw [ih,ih]
    · rw [entry_ofFn_out _ (by omega),Int.cast_zero]
      apply Eq.symm
      apply coeff_eq_zero_of_natDegree_lt
      rw [(eulerian_monic_degree (R := ℝ) (n+1) (by omega)).natDegree_eq]
      omega

def convolutionPrefix (a b : Array ℤ) (k : ℕ) : ℕ → ℤ
  | 0 => 0
  | i+1 => convolutionPrefix a b k i + rowEntry a i*rowEntry b (k-i)

private theorem convolutionPrefix_eq (a b : Array ℤ) (k m : ℕ) :
    convolutionPrefix a b k m = ∑ i∈Finset.range m,rowEntry a i*rowEntry b (k-i) := by
  induction m with
  | zero => simp [convolutionPrefix]
  | succ m ih => rw [convolutionPrefix,Finset.sum_range_succ,ih]

def reducedEntry (all l r : Array ℤ) : ℕ → ℤ
  | 0 => rowEntry all 0
  | k+1 => rowEntry all (k+1)-convolutionPrefix l r k (k+1)

def combineRows (n : ℕ) (all l r : Array ℤ) : List ℤ :=
  (Array.ofFn fun i : Fin n => reducedEntry all l r i.val).toList

theorem combineRows_eq_of_entries {n : ℕ} {p : List ℤ} {all l r : Array ℤ}
    (hlen : p.length=n)
    (entries : ∀ i : Fin n,p[i.val]?.getD 0=reducedEntry all l r i.val) :
    p=combineRows n all l r := by
  apply List.ext_getElem (by simp [combineRows,hlen])
  intro i hp _
  simpa [combineRows,List.getElem?_eq_getElem hp] using entries ⟨i,hlen ▸ hp⟩

abbrev entriesFrom (P : ℕ → Prop) (start count : ℕ) := ∀ i : Fin count,P (start+i.val)

theorem entriesFrom_zero {P : ℕ → Prop} {n : ℕ} (h : entriesFrom P 0 n) :
    ∀ i : Fin n,P i.val := by
  intro i
  simpa only [Nat.zero_add] using h i

theorem entriesFrom_join {P : ℕ → Prop} {s n m : ℕ}
    (left : entriesFrom P s n) (right : entriesFrom P (s+n) m) : entriesFrom P s (n+m) := by
  intro i
  by_cases h : i.val<n
  · exact left ⟨i.val,h⟩
  · have small : i.val-n<m := by omega
    have eq : s+n+(i.val-n)=s+i.val := by omega
    simpa only [eq] using right ⟨i.val-n,small⟩

def reducedRow (n : ℕ) : List ℤ :=
  combineRows n (eulerRows n) (eulerRows (leftSize n)) (eulerRows (rightSize n))

theorem coefficient_polynomialOfRow (c : List ℤ) (k : ℕ) :
    (polynomialOfRow c).coeff k=(c[k]?.getD 0 : ℤ) := by
  induction c generalizing k with
  | nil => simp [polynomialOfRow]
  | cons a c ih =>
    cases k with
    | zero => simp [polynomialOfRow]
    | succ k =>
      rw [polynomialOfRow,coeff_add,coeff_C,coeff_X_mul,ih]
      simp

theorem reduced_row_correct (n : ℕ) (hn : 3≤n) :
    polynomialOfRow (reducedRow n)=reducedRevstack (R := ℝ) n := by
  ext k
  rw [coefficient_polynomialOfRow]
  unfold reducedRow combineRows
  rw [Array.getElem?_toList]
  change (rowEntry (Array.ofFn _) k : ℝ)=_
  by_cases h : k<n
  · rw [entry_ofFn _ h]
    cases k with
    | zero => simp [reducedEntry,euler_row_correct,coeff_zero_eq_eval_zero]
    | succ k =>
      rw [reducedRevstack,coeff_sub,coeff_X_mul,coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [reducedEntry,convolutionPrefix_eq,euler_row_correct]
  · rw [entry_ofFn_out _ (by omega),Int.cast_zero]
    exact (coeff_eq_zero_of_natDegree_lt (by rw [(reducedRevstack_monic_degree n hn).natDegree_eq]; omega)).symm

end DukesRevstack
