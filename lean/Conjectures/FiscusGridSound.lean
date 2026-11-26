import Conjectures.FiscusGridTable

/-! Pointwise correctness of the certificate table implies the game value on
the actual graph. The induction decreases with each new selection. -/

namespace FiscusGrid

private theorem next_small {s : ℕ} (hs : s<2^14) (i : Fin 14) : s ||| 2^i.val < 2^14 :=
  Nat.or_lt_two_pow hs (Nat.pow_lt_pow_right (by decide) i.isLt)

private theorem next_grows (s : ℕ) (i : Fin 14) (free : s.testBit i.val=false) : s<s ||| 2^i.val := by
  refine lt_of_le_of_ne Nat.left_le_or ?_
  intro eq
  have bit : (s ||| 2^i.val).testBit i.val=true := by simp
  rw [←eq,free] at bit
  contradiction

theorem table_sound (check : ∀ s<2^14, consistent s=true) (s : ℕ) (hs : s<2^14) :
    value s=true ↔ Wins (grid 2 7) (picked s) := by
  induction rank : 2^14-s using Nat.strong_induction_on generalizing s with
  | h n ih =>
    have next (i : Fin 14) (hi : s.testBit i.val=false) :
        value (s ||| 2^i.val)=true ↔ Wins (grid 2 7) (insert (vertex i) (picked s)) := by
      rw [←picked_insert]
      have small := next_small hs i
      have grow := next_grows s i hi
      exact ih _ (by omega) _ small rfl
    rw [consistent_spec (check s hs),wins_iff]
    have cov := covered_iff s hs
    constructor
    · rintro ⟨c,i,free,loss⟩
      refine ⟨fun dom => by simp [c] at cov; exact cov dom,vertex i,?_,?_⟩
      · simp [free]
      · intro win
        have yes := (next i free).mpr win
        simp [loss] at yes
    · rintro ⟨c,p,free,loss⟩
      have hfree : s.testBit (number p).val=false := by simpa using free
      refine ⟨by cases h : covered s <;> simp_all,number p,hfree,?_⟩
      have no : ¬Wins (grid 2 7) (insert (vertex (number p)) (picked s)) := by simpa using loss
      cases h : value (s ||| 2^(number p).val)
      · rfl
      · exact False.elim (no ((next _ hfree).mp h))

end FiscusGrid
