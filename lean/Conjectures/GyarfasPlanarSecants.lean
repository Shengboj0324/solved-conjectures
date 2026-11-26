import Conjectures.GyarfasPlanarWitness
import Mathlib.Tactic.Positivity

/-! The directions between the listed rational points. The formulas classify
all coincidences between secants and lines meeting the vertical axis. -/

namespace GyarfasPlanar

def secant (i j : ℕ) : ℚ := 1-((i : ℚ)+1)*((j : ℚ)+1)
def axisSlope (i : ℕ) (s : ℤ) : ℚ := (i : ℚ)^2-((i : ℚ)+1)*(s : ℚ)

theorem off_fst_injective : Function.Injective (fun i => (offAxis i).1) := by
  intro i j h
  change 1/((i : ℚ)+1)=1/((j : ℚ)+1) at h
  have hi : (i : ℚ)+1≠0 := by positivity
  have hj : (j : ℚ)+1≠0 := by positivity
  field_simp at h
  exact_mod_cast (show (i : ℚ)=(j : ℚ) by linarith)

theorem off_injective : Function.Injective offAxis :=
  fun _ _ h => off_fst_injective (congrArg Prod.fst h)

theorem on_injective : Function.Injective onAxis := by
  intro i j h
  exact_mod_cast (show (i : ℚ)=(j : ℚ) from congrArg Prod.snd h)

theorem off_fst_ne (i : ℕ) : (offAxis i).1≠0 := by
  change 1/((i : ℚ)+1)≠0
  positivity

theorem off_ne_on (i : ℕ) (s : ℤ) : offAxis i≠onAxis s := fun e =>
  off_fst_ne i (congrArg Prod.fst e)

theorem direction_swap (p q : Point ℚ) : direction p q=direction q p := by
  by_cases h : q.1=p.1
  · simp [direction,h]
  · simp only [direction,ite_eq_right h,ite_eq_right (Ne.symm h),Option.some.injEq]
    apply (div_eq_div_iff (sub_ne_zero.mpr h) (sub_ne_zero.mpr (Ne.symm h))).mpr
    ring

theorem off_secant {i j : ℕ} (h : j≠i) : direction (offAxis i) (offAxis j)=some (secant i j) := by
  have ne : (offAxis j).1≠(offAxis i).1 := fun e => h (off_fst_injective e)
  rw [direction,ite_eq_right ne,Option.some.injEq]
  apply (div_eq_iff (sub_ne_zero.mpr ne)).mpr
  dsimp [offAxis,secant]
  have hi : (i : ℚ)+1≠0 := by positivity
  have hj : (j : ℚ)+1≠0 := by positivity
  field_simp
  ring

theorem axis_secant (i : ℕ) (s : ℤ) : direction (onAxis s) (offAxis i)=some (axisSlope i s) := by
  have ne : (offAxis i).1≠(onAxis s).1 := off_fst_ne i
  rw [direction,ite_eq_right ne,Option.some.injEq]
  apply (div_eq_iff (sub_ne_zero.mpr (off_fst_ne i))).mpr
  dsimp [offAxis,onAxis,axisSlope]
  have hi : (i : ℚ)+1≠0 := by positivity
  field_simp
  ring

theorem off_secant_injective (i : ℕ) : Function.Injective (secant i) := by
  intro j l h
  have hi : (i : ℚ)+1≠0 := by positivity
  have eq : ((i : ℚ)+1)*((j : ℚ)+1)=((i : ℚ)+1)*((l : ℚ)+1) := by
    unfold secant at h
    linarith
  have hh := mul_left_cancel₀ hi eq
  exact_mod_cast (show (j : ℚ)=(l : ℚ) by linarith)

theorem at_off_axis_injective (i : ℕ) : Function.Injective (axisSlope i) := by
  intro s t h
  have hi : (i : ℚ)+1≠0 := by positivity
  have eq : ((i : ℚ)+1)*(s : ℚ)=((i : ℚ)+1)*(t : ℚ) := by
    unfold axisSlope at h
    linarith
  exact_mod_cast mul_left_cancel₀ hi eq

theorem shared_intercept (i j : ℕ) (s : ℤ) :
    secant i j=axisSlope i s ↔ s=(i : ℤ)+j := by
  have hp : (i : ℚ)+1≠0 := by positivity
  have form : secant i j-axisSlope i s=((i : ℚ)+1)*((s : ℚ)-(i : ℚ)-j) := by
    unfold secant axisSlope
    ring
  rw [←sub_eq_zero,form,mul_eq_zero,or_iff_right hp]
  constructor
  · intro h
    exact_mod_cast (show (s : ℚ)=i+j by linarith)
  · intro h
    exact_mod_cast (show s-(i : ℤ)-j=0 by omega)

theorem axis_collisions (s : ℤ) (i j : ℕ) :
    axisSlope i s=axisSlope j s ↔ i=j ∨ s=(i : ℤ)+j := by
  have form : axisSlope i s-axisSlope j s=((i : ℚ)-j)*((i : ℚ)+j-s) := by
    unfold axisSlope
    ring
  rw [←sub_eq_zero,form,mul_eq_zero,sub_eq_zero,sub_eq_zero]
  constructor
  · rintro (h|h)
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h.symm)
  · rintro (h|h)
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h.symm)

end GyarfasPlanar
