import Conjectures.FiscusGridCertificate
import Conjectures.FiscusGridSound

/-! For the ordinary game on two paths' Cartesian product, the winning
first moves are precisely the vertices in the second and sixth columns. -/

namespace FiscusGrid

theorem picked_empty : picked 0=∅ := by ext p; simp

theorem picked_one (i : Fin 14) : picked (2^i.val) = {vertex i} := by
  simpa [picked_empty] using picked_insert 0 i

theorem first_wins : Wins (grid 2 7) ∅ := by
  rw [←picked_empty]
  exact (table_sound certificate 0 (by decide)).mp (by decide)

theorem winning_openings (p : Vertex) : ¬Wins (grid 2 7) {p} ↔
    p.2.val=1 ∨ p.2.val=5 := by
  have small : 2^(number p).val<2^14 := Nat.pow_lt_pow_right (by decide) (number p).isLt
  have state := table_sound certificate _ small
  rw [picked_one,vertex_number] at state
  have openings : ∀ i : Fin 14, value (2^i.val)=false ↔ (vertex i).2.val=1 ∨ (vertex i).2.val=5 := by decide
  have result := openings (number p)
  rw [vertex_number] at result
  rw [←result,←state]
  cases value (2^(number p).val) <;> decide

theorem not_even_grid_conjecture :
    ¬(∀ a b : ℕ, 1<a → 1<b → Even (a*b) → ¬Wins (grid a b) ∅) := by
  intro claim
  exact claim 2 7 (by decide) (by decide) (by decide) first_wins

end FiscusGrid
