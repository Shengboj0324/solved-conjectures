import Conjectures.TransportationEhrhartCount
import Conjectures.TransportationBinomial
import Conjectures.TransportationPolynomial
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! The ordinary generating series of genuine table counts. Multiplication by
(1-X)^(2m+1) recovers the real polynomial used in the root certificate. -/

namespace TransportationEhrhart

noncomputable def tableSeries (m : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => (Nat.card (Table m k) : ℝ)

noncomputable def binomialSeries (d : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => ((d+n).choose d : ℝ)

theorem shifted_coefficient (d k j : ℕ) (hd : 0<d) :
    PowerSeries.coeff k (PowerSeries.X^j*binomialSeries d)=((k+d-j).choose d : ℝ) := by
  rw [mul_comm,PowerSeries.coeff_mul_X_pow']
  by_cases le : j≤k
  · rw [ite_eq_left le,binomialSeries,PowerSeries.coeff_mk]
    congr 2
    omega
  · rw [ite_eq_right le,Nat.choose_eq_zero_of_lt (show k+d-j<d by omega),Nat.cast_zero]

theorem count_add_correction {m : ℕ} (hm : 0<m) (k : ℕ) :
    Nat.card (Table m k)+m*(k+2*m-1).choose (2*m)=(k+m).choose m^2 := by
  cases k with
  | zero =>
    have small := Nat.choose_eq_zero_of_lt (show 2*m-1<2*m by omega)
    simp [table_count_zero,small]
  | succ k =>
    have eq : k+1+2*m-1=2*m+k := by omega
    simpa only [eq] using table_count_succ m k

theorem real_count_formula {m : ℕ} (hm : 0<m) (k : ℕ) :
    (Nat.card (Table m k) : ℝ) =
     (∑ j ∈ Finset.range (m+1),(m.choose j : ℝ)^2*((k+2*m-j).choose (2*m) : ℝ))-
      (m : ℝ)*((k+2*m-1).choose (2*m) : ℝ) := by
  have sqr : (∑ j ∈ Finset.range (m+1),(m.choose j : ℝ)^2*((k+2*m-j).choose (2*m) : ℝ)) =
      ((k+m).choose m : ℝ)^2 := by exact_mod_cast square_binomial_series m k
  rw [sqr,eq_sub_iff_add_eq]
  exact_mod_cast count_add_correction hm k

theorem series_identity {m : ℕ} (hm : 0<m) :
    tableSeries m = (numerator m : PowerSeries ℝ)*binomialSeries (2*m) := by
  ext k
  rw [tableSeries,PowerSeries.coeff_mk,real_count_formula hm]
  let f : Polynomial ℝ →+* PowerSeries ℝ := Polynomial.coeToPowerSeries.ringHom
  change _=PowerSeries.coeff k (f (numerator m)*_)
  simp only [numerator,map_sub,map_sum,map_mul,map_pow,sub_mul,Finset.sum_mul,map_sub,map_sum]
  have mappedC (a : ℝ) : f (Polynomial.C a)=PowerSeries.C a := Polynomial.coe_C a
  have mappedX : f Polynomial.X=PowerSeries.X := Polynomial.coe_X
  simp only [mappedC,mappedX,←map_pow PowerSeries.C]
  change _=(∑ j ∈ Finset.range (m+1),PowerSeries.coeff k
    (PowerSeries.C ((m.choose j : ℝ)^2)*PowerSeries.X^j*binomialSeries (2*m)))-
    PowerSeries.coeff k (PowerSeries.C (m : ℝ)*PowerSeries.X*binomialSeries (2*m))
  have pos : 0<2*m := by omega
  have last := shifted_coefficient (2*m) k 1 pos
  rw [pow_one] at last
  simp only [mul_assoc,PowerSeries.coeff_C_mul,shifted_coefficient _ _ _ pos,last]

theorem ehrhart_numerator {m : ℕ} (hm : 0<m) :
    tableSeries m*(1-PowerSeries.X)^(2*m+1)=(numerator m : PowerSeries ℝ) := by
  rw [series_identity hm,mul_assoc]
  have unit : binomialSeries (2*m)*(1-PowerSeries.X)^(2*m+1) = 1 :=
    PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℝ (2*m)
  rw [unit,mul_one]

end TransportationEhrhart
