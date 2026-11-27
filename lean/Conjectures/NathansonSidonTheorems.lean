import Conjectures.NathansonSidonGcd
import Conjectures.NathansonSidonLimit

/-! Nathanson's three questions in §6 of The Bose–Chowla argument for Sidon sets.
The unrestricted multiplicity-one assertion also covers any additional prime
restrictions, and multiplicity may be increased to the factorial of the arity. -/

open Filter

namespace NathansonSidon

theorem nathanson_three_questions {h : ℕ} (hh : 2≤h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0) :
    (1≤positionalConstant (by omega) c) ∧
    (positionalConstant (by omega) c≤liminf (normalized c 1) atTop) ∧
    (1≤liminf (normalized c h.factorial) atTop) :=
  ⟨one_le_positionalConstant (by omega) c nz,positional_liminf hh c nz le_rfl,
    nathanson_factorial hh c nz⟩

end NathansonSidon
