import Conjectures.FiscusGridGame

/-! Packed positions from the 2-by-7 grid. Each neighborhood mask is checked
against the Cartesian product of the two mathlib path graphs. -/

namespace FiscusGrid

def hood (i : Fin 14) : ℕ :=
  [131,263,526,1052,2104,4208,8288,385,898,1796,3592,7184,14368,12352].getD i.val 0

private theorem mask_edges : ∀ i j : Fin 14,
    (hood j).testBit i.val = decide (vertex i=vertex j ∨
      ((vertex i).1.val+1=(vertex j).1.val ∨ (vertex j).1.val+1=(vertex i).1.val) ∧
        (vertex i).2=(vertex j).2 ∨
      ((vertex i).2.val+1=(vertex j).2.val ∨ (vertex j).2.val+1=(vertex i).2.val) ∧
        (vertex i).1=(vertex j).1) := by decide

theorem hood_closed (i j : Fin 14) : (hood j).testBit i.val = true ↔
    vertex i=vertex j ∨ (grid 2 7).Adj (vertex i) (vertex j) := by
  rw [mask_edges]
  simp only [decide_eq_true_eq,grid,SimpleGraph.boxProd_adj,SimpleGraph.pathGraph_adj]

def covered (s : ℕ) : Bool :=
  (List.finRange 14).all fun j => (s &&& hood j) != 0

private theorem overlaps (s : ℕ) (j : Fin 14) (hs : s<2^14) :
    s &&& hood j ≠ 0 ↔ ∃ i : Fin 14, s.testBit i.val=true ∧ (hood j).testBit i.val=true := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero h
    rw [Nat.testBit_and,Bool.and_eq_true] at hi
    have small : i<14 := by
      by_contra! hn
      have b : s<2^i := lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) hn)
      rw [Nat.testBit_lt_two_pow b] at hi
      simp at hi
    exact ⟨⟨i,small⟩,hi⟩
  · rintro ⟨i,a,b⟩ z
    have bit : (s &&& hood j).testBit i.val=true := by simp [Nat.testBit_and,a,b]
    simp [z] at bit

theorem covered_iff (s : ℕ) (hs : s<2^14) : covered s=true ↔ Dominates (grid 2 7) (picked s) := by
  simp only [covered,List.all_eq_true,List.mem_finRange,forall_const,bne_iff_ne]
  constructor
  · intro h p
    obtain ⟨i,hi,near⟩ := (overlaps s (number p) hs).mp (h (number p))
    refine ⟨vertex i,by simpa using hi,?_⟩
    simpa only [vertex_number] using (hood_closed i (number p)).mp near
  · intro h j
    obtain ⟨p,hp,near⟩ := h (vertex j)
    apply (overlaps s j hs).mpr
    refine ⟨number p,(mem_picked s p).mp hp,(hood_closed _ j).mpr ?_⟩
    simpa using near

end FiscusGrid
