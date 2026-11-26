import Mathlib.Tactic.IntervalCases

/-! Split a finite vertex-table check into separately kernel-checked groups
of sixteen rows. Wrapping the final group also covers a partial last group. -/

namespace CircularIndex.Deleted

def rowBlock {n : ℕ} [NeZero n] (P : Fin n → Prop) (b : ℕ) : Prop :=
  ∀ i : Fin 16, P (Fin.ofNat n (16*b+i.val))

theorem all_rows_of_blocks {n : ℕ} [NeZero n] {P : Fin n → Prop}
    (h : ∀ b : Fin ((n+15)/16), rowBlock P b.val) (v : Fin n) : P v := by
  have hv := v.isLt
  let b : Fin ((n+15)/16) := ⟨v.val/16,by omega⟩
  let i : Fin 16 := ⟨v.val%16,Nat.mod_lt _ (by decide)⟩
  have e : Fin.ofNat n (16*b.val+i.val)=v := by
    apply Fin.ext
    change (16*(v.val/16)+v.val%16)%n=v.val
    rw [show 16*(v.val/16)+v.val%16=v.val by omega,Nat.mod_eq_of_lt hv]
  exact e ▸ h b i

end CircularIndex.Deleted
