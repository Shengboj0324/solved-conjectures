import Conjectures.ErdosGyarfasSpectrumArithmetic
import Conjectures.ErdosGyarfasSpectrumComparison
import Conjectures.ErdosGyarfasSpectrumRepresentatives

/-! The degree deficit is at least one seventeenth of the order, with the
additive constant from the finite theorem. -/

namespace ErdosGyarfasSpectrum

variable {V : Type*} [DecidableEq V] {P : Finset V} {lines : Finset (Finset V)}

theorem spectrum_bound (space : LinearOn P lines) :
    17*(degrees P lines).card+13 ≤ 16*P.card := by
  let f := (degrees P lines).card
  let t := f/2
  change 17*f+13 ≤ 16*P.card
  have fn : f<P.card := degrees_lt_order space
  have n := space.order
  by_cases small : f≤3
  · omega
  obtain ⟨X,Y,hX,hY,d,hx,hy,low,high⟩ := representative_sets space (f := f) (t := t) rfl rfl (by omega)
  obtain ⟨nonneg,C,_,c,cs⟩ := two_set_comparison space hX hY d hx hy
  have tw : 2 ≤ (t : ℤ) := by dsimp [t]; omega
  have m : 0 ≤ (P.card : ℤ)-f-1 := by omega
  have b := half_bound tw m nonneg high low c cs
  have half : f≤2*t+1 := by dsimp [t]; omega
  omega

theorem degree_deficit (space : LinearOn P lines) :
    P.card+13 ≤ 17*(P.card-(degrees P lines).card) := by
  have h := spectrum_bound space
  have d := degrees_lt_order space
  omega

end ErdosGyarfasSpectrum
