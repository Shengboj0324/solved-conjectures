import Conjectures.GyarfasPlanarSpectrum
import Conjectures.GyarfasPlanarWitness

/-! The same rational configuration witnesses optimal multiplicity and
the stated exact number of distinct real spanned-line degrees at every order. -/

namespace GyarfasPlanar

theorem every_order_with_spectrum {n : ℕ} (hn : 16 ≤ n) :
    ∃ S : Finset (Point ℚ), let P := S.image realPoint
      P.card=n ∧ ¬Collinear ℝ (↑P : Set (Point ℝ)) ∧
      (∀ d, multiplicity P d ≤ 2) ∧ (∃ d, multiplicity P d=2) ∧
      (spectrum P).card = n/2+(n/2)/2-3+n%2 ∧
      4*(spectrum P).card+11 ≤ 3*n ∧ 3*n ≤ 4*(spectrum P).card+14 := by
  let k := n/2
  let odd := decide (n%2=1)
  have hk : 8 ≤ k := by dsimp [k]; omega
  have parity : odd.toNat=n%2 := by
    dsimp [odd]
    by_cases h : n%2=1
    · simp [h]
    · simp [h]; omega
  have size : 2*k+odd.toNat=n := by rw [parity]; dsimp [k]; omega
  obtain ⟨card,geom,upper,attains⟩ := uniform_real hk odd
  have count := spectrum_card hk odd
  have err := spectrum_error hk odd
  rw [size] at err
  rw [parity] at count
  exact ⟨configuration k odd,card.trans size,geom,upper,attains,count,err⟩

end GyarfasPlanar
