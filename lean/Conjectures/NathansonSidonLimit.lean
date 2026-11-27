import Conjectures.NathansonSidonOrder
import Conjectures.NathansonSidonRounding
import Conjectures.NathansonSidonDiameter

/-! The coefficient-adjusted positional construction gives a lower bound at
every sufficiently large order and hence for Nathanson's actual limit inferior. -/

open Filter

namespace NathansonSidon

variable {h : ℕ}

def minWeight (hh : 0<h) (c : Fin h → ℤ) : ℕ :=
  Finset.univ.inf' ⟨firstIndex hh,Finset.mem_univ _⟩ fun i => (c i).natAbs

def maxWeight (c : Fin h → ℤ) : ℕ := Finset.univ.sup fun i => (c i).natAbs

noncomputable def normalized (c : Fin h → ℤ) (g N : ℕ) : ℝ :=
  (extremal c N g : ℝ)/radius h N

noncomputable def positionalConstant (hh : 0<h) (c : Fin h → ℤ) : ℝ :=
  ((maxWeight c : ℝ)/(minWeight hh c : ℝ))^((h : ℝ)⁻¹)

theorem normalized_bounded (hh : 0<h) (c : Fin h → ℤ) (g : ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (normalized c g) := by
  let C := g*(coefficientSum c+1)
  refine ⟨(C : ℝ),?_⟩
  change ∀ᶠ N : ℕ in atTop,normalized c g N≤(C : ℝ)
  filter_upwards [eventually_ge_atTop 1] with N npos
  have count := extremal_diameter hh c N g
  have wid : coefficientSum c*(N-1)+1≤(coefficientSum c+1)*N := by
    rw [Nat.add_mul,one_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) npos
  have bound : (extremal c N g)^h≤C^h*N := calc
    _ ≤ g*(coefficientSum c*(N-1)+1) := count
    _ ≤ g*((coefficientSum c+1)*N) := Nat.mul_le_mul_left g wid
    _ = C*N := (Nat.mul_assoc _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_pow hh)
  have realBound : (extremal c N g : ℝ)^h≤(C : ℝ)^h*(N : ℝ) := by exact_mod_cast bound
  have pos : 0<radius h N := Real.rpow_pos_of_pos (by exact_mod_cast (show 0<N by omega)) _
  apply (div_le_iff₀ pos).mpr
  by_contra! bad
  have strict := pow_lt_pow_left₀ bad (mul_nonneg (Nat.cast_nonneg C) pos.le) (Nat.ne_of_gt hh)
  rw [mul_pow,radius_pow hh] at strict
  exact (not_lt_of_ge realBound) strict

theorem positional_eventually {g : ℕ} (hh : 2≤h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0)
    (hg : 1≤g) (d : ℝ) (below : d<positionalConstant (by omega) c) :
    ∀ᶠ N : ℕ in atTop,d≤normalized c g N := by
  have hp : 0<h := by omega
  obtain ⟨e,least,greatest⟩ := arranged hh fun i => (c i).natAbs
  let a := c ∘ e
  let u := (a (firstIndex hp)).natAbs
  let v := (a (lastIndex hp)).natAbs
  have hmin : minWeight hp c=u := le_antisymm
    (Finset.inf'_le _ (Finset.mem_univ (e (firstIndex hp))))
    (Finset.le_inf' _ _ fun i _ => least i)
  have hmax : maxWeight c=v := le_antisymm
    (Finset.sup_le fun i _ => greatest i)
    (Finset.le_sup (f := fun i => (c i).natAbs) (Finset.mem_univ (e (lastIndex hp))))
  have az : ∀ i,a i≠0 := fun i => nz (e i)
  have hu : 0<u := Int.natAbs_pos.mpr (az _)
  have hv : 0<v := Int.natAbs_pos.mpr (az _)
  unfold positionalConstant at below
  rw [hmin,hmax] at below
  have bases := rounded_bases hp (period_pos a az) hu hv d below
  filter_upwards [bases,eventually_ge_atTop 1] with N base npos
  obtain ⟨r,multi,hr,large,room,ratio⟩ := base
  have w := finite_system hp a az hr multi (fun i => least (e i)) large room
  have f := feasible_mono_multiplicity hg ((feasible_reindex e c).mpr w)
  have fit := feasible_le_extremal hp f
  have pos : 0<radius h N := Real.rpow_pos_of_pos (by exact_mod_cast (show 0<N by omega)) _
  exact ratio.trans (div_le_div_of_nonneg_right (by exact_mod_cast fit) pos.le)

theorem positional_liminf {g : ℕ} (hh : 2≤h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0) (hg : 1≤g) :
    positionalConstant (by omega) c≤liminf (normalized c g) atTop := by
  by_contra! fail
  obtain ⟨d,above,below⟩ := exists_between fail
  exact above.not_ge (le_liminf_of_le (normalized_bounded (by omega) c g).isCoboundedUnder_ge
    (positional_eventually hh c nz hg d below))

theorem one_le_positionalConstant (hh : 0<h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0) :
    1≤positionalConstant hh c := by
  have lo : 0<minWeight hh c := by
    change 1≤Finset.univ.inf' _ (fun i => (c i).natAbs)
    exact Finset.le_inf' _ _ fun i _ => Int.natAbs_pos.mpr (nz i)
  have order : minWeight hh c≤maxWeight c :=
    (Finset.inf'_le (fun i => (c i).natAbs) (Finset.mem_univ (firstIndex hh))).trans
      (Finset.le_sup (f := fun i => (c i).natAbs) (Finset.mem_univ (firstIndex hh)))
  apply Real.one_le_rpow
  · apply (one_le_div (by exact_mod_cast lo)).mpr
    exact_mod_cast order
  · positivity

theorem nathanson_multiplicity_one (hh : 2≤h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0) :
    1≤liminf (normalized c 1) atTop :=
  (one_le_positionalConstant (by omega) c nz).trans (positional_liminf hh c nz le_rfl)

theorem nathanson_factorial (hh : 2≤h) (c : Fin h → ℤ) (nz : ∀ i,c i≠0) :
    1≤liminf (normalized c h.factorial) atTop :=
  (one_le_positionalConstant (by omega) c nz).trans (positional_liminf hh c nz (Nat.factorial_pos _))

end NathansonSidon
