import Conjectures.AlexanderssonParkingExcedanceEnumeration
import Conjectures.AlexanderssonParkingExcedanceRoots
import Conjectures.AlexanderssonParkingExcedanceTables

/-! The length-17 counting certificate and the disproof for the actual polynomial. -/

namespace AlexanderssonParkingExcedance

open Finset Polynomial

private theorem fastChoose_eq (n k : ℕ) : fastChoose n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

private theorem table_correct {n j : ℕ} (hj : j ≤ n) (i k : Fin (n + 1)) :
    (table n j)[i.val][k.val] = Fintype.card (State n j i k) := by
  induction j generalizing i k with
  | zero => simp [table, initialTable, state_card_zero]
  | succ j IH =>
    simp only [table, nextTable, Vector.getElem_ofFn]
    by_cases h : j + 1 ≤ i.val + k.val ∧ i.val + k.val ≤ n
    · rw [ite_eq_left h, state_card_succ (by omega) h.1 h.2]
      simp only [List.sum_ofFn, fastChoose_eq]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      exact congrArg (fun x : ℕ => x * (j - b.val).choose (k.val - b.val) *
        i.val.choose (i.val - a.val)) (IH (by omega) ⟨a.val, by omega⟩ ⟨b.val, by omega⟩)
    · rw [ite_eq_right h, state_card_invalid h]

private noncomputable def shiftedOfList : List ℕ → ℝ[X]
  | [] => 0
  | a :: as => C (a : ℝ) + (X - 1) * shiftedOfList as

private theorem shiftedOfList_ofFn {m : ℕ} (f : Fin m → ℕ) :
    shiftedOfList (List.ofFn f) = ∑ k : Fin m, (f k : ℝ[X]) * (X - 1) ^ k.val := by
  induction m with
  | zero => simp [shiftedOfList]
  | succ m IH =>
    rw [List.ofFn_succ, shiftedOfList, IH, Fin.sum_univ_succ, mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, C_eq_natCast]
    congr 1
    exact sum_congr rfl fun k _ => by ring

private theorem polynomial_eq_shifted (n : ℕ) :
    polynomial n = shiftedOfList (markedCounts n) := by
  rw [polynomial_eq_state_sum, markedCounts, shiftedOfList_ofFn, Finset.sum_range]
  apply sum_congr rfl
  intro k _
  rw [table_correct le_rfl ⟨n - k.val, by omega⟩ k]

/-- The exact coefficient row belongs to the literal parking-word enumerator. -/
theorem polynomial17_eq_row : polynomial 17 = polynomialOfList row17 := by
  rw [polynomial_eq_shifted, markedCounts17_eq]
  norm_num [markedRow17, row17, shiftedOfList, polynomialOfList, map_ofNat]
  ring

/-- The actual excedance polynomial for length 17 has a nonreal root. -/
theorem parking_excedance_counterexample :
    ∃ z : ℂ, ((polynomial 17).map Complex.ofRealHom).IsRoot z ∧ z.im ≠ 0 := by
  rw [polynomial17_eq_row]
  exact row17_nonreal_root

end AlexanderssonParkingExcedance
