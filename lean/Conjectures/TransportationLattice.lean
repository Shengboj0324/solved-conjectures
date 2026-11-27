import Conjectures.TransportationPolytope
import Conjectures.TransportationSeries

/-! Identify the coefficients with the actual integer points of scalar
dilates of the real matrix polytope. -/

namespace TransportationEhrhart

open scoped Pointwise

abbrev IntegralPoints (m k : ℕ) := {z : Fin 3 → Col m → ℤ //
  (fun i j => (z i j : ℝ)) ∈ (k : ℝ) • polytope m}

def tableReal {m k : ℕ} (t : Table m k) : RealTable m := fun i j => (t.val i j : ℝ)

theorem tableReal_fits {m k : ℕ} (t : Table m k) : fits m k (tableReal t) := by
  refine ⟨fun _ _ => Nat.cast_nonneg _,?_,?_⟩
  · intro i
    change ∑ j,(t.val i j : ℝ)=_
    exact_mod_cast t.property.1 i
  · intro j
    change ∑ i,(t.val i j : ℝ)=_
    exact_mod_cast t.property.2 j

theorem integer_fits {m k : ℕ} (z : IntegralPoints m k) :
    (∀ i j,0≤z.val i j) ∧ (∀ i,∑ j,z.val i j=(rowMargin m k i : ℤ)) ∧
      ∀ j,∑ i,z.val i j=(capacity k j : ℤ) := by
  obtain ⟨nonneg,row,col⟩ := mem_dilate.mp z.property
  dsimp only at nonneg row col
  refine ⟨fun i j => ?_,fun i => ?_,fun j => ?_⟩
  · exact_mod_cast nonneg i j
  · exact_mod_cast row i
  · exact_mod_cast col j

def fromIntegral {m k : ℕ} (z : IntegralPoints m k) : Table m k :=
  ⟨fun i j => (z.val i j).toNat,by
    obtain ⟨pos,row,col⟩ := integer_fits z
    constructor
    · intro i
      apply Int.ofNat_inj.mp
      push_cast
      simp only [Int.toNat_of_nonneg (pos _ _)]
      exact row i
    · intro j
      apply Int.ofNat_inj.mp
      push_cast
      simp only [Int.toNat_of_nonneg (pos _ _)]
      exact col j⟩

def integralEquiv (m k : ℕ) : Table m k ≃ IntegralPoints m k where
  toFun t := ⟨fun i j => (t.val i j : ℤ),by
    change (fun i j => ((t.val i j : ℤ) : ℝ)) ∈ (k : ℝ) • polytope m
    simp only [Int.cast_natCast]
    exact mem_dilate.mpr (tableReal_fits t)⟩
  invFun := fromIntegral
  left_inv t := by
    apply Subtype.ext
    funext i j
    exact Int.toNat_natCast _
  right_inv z := by
    apply Subtype.ext
    funext i j
    exact Int.toNat_of_nonneg ((integer_fits z).1 i j)

noncomputable def ehrhartSeries (m : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => (Nat.card (IntegralPoints m k) : ℝ))

theorem ehrhart_eq_table (m : ℕ) : ehrhartSeries m=tableSeries m := by
  ext k
  simp only [ehrhartSeries,tableSeries,PowerSeries.coeff_mk]
  exact_mod_cast (Nat.card_congr (integralEquiv m k)).symm

theorem integer_points_numerator {m : ℕ} (hm : 0<m) :
    ehrhartSeries m*(1-PowerSeries.X)^(2*m+1)=(numerator m : PowerSeries ℝ) := by
  rw [ehrhart_eq_table,ehrhart_numerator hm]

end TransportationEhrhart
