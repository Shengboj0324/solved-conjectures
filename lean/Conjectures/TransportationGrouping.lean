import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Tactic

/-! Splitting row and column margins into unit slots identifies a
transportation matrix with the grouped entries of a doubly stochastic matrix. -/

namespace TransportationEhrhart

open Finset Matrix

variable {ι A B : Type*} [Fintype ι] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

def fiber {K : Type*} [DecidableEq K] (label : ι → K) (b : K) : Finset ι :=
  univ.filter fun t => label t=b

theorem mem_fiber {K : Type*} [DecidableEq K] {g : ι → K} {b : K} {x : ι} :
    x∈fiber g b ↔ g x=b := by simp [fiber]

theorem sum_over_labels (g : ι → A) {R : Type*} [AddCommMonoid R] (f : ι → R) :
    ∑ b,∑ x ∈ fiber g b,f x=∑ x,f x := sum_fiberwise univ g f

theorem normalized_slot_sum (g : ι → A) (pos : ∀ b,0<(fiber g b).card) (v : A → ℝ) :
    ∑ x,v (g x)/(fiber g (g x)).card=∑ b,v b := by
  rw [←sum_over_labels g]
  apply sum_congr rfl
  intro b _
  calc
    _ = ∑ _x ∈ fiber g b,v b/(fiber g b).card := by
      apply sum_congr rfl
      intro x hx
      rw [mem_fiber.mp hx]
    _ = _ := by
      have nz : ((fiber g b).card : ℝ)≠0 := by exact_mod_cast (pos b).ne'
      simp [nsmul_eq_mul, mul_div_cancel₀, nz]

def grouped {R : Type*} [AddCommMonoid R] (r : ι → A) (c : ι → B) (x : Matrix ι ι R) (i : A) (j : B) : R :=
  ∑ t ∈ fiber r i,∑ s ∈ fiber c j,x t s

noncomputable def grouping (r : ι → A) (c : ι → B) : Matrix ι ι ℝ →ₗ[ℝ] (A → B → ℝ) where
  toFun := grouped r c
  map_add' x y := by
    funext i j
    simp only [grouped, Matrix.add_apply,Finset.sum_add_distrib,Pi.add_apply]
  map_smul' z x := by
    funext i j
    simp only [grouped,Matrix.smul_apply,Pi.smul_apply,RingHom.id_apply,smul_eq_mul,Finset.mul_sum]

noncomputable def expandSlots (r : ι → A) (c : ι → B) (a : A → B → ℝ) : Matrix ι ι ℝ :=
  fun t s => a (r t) (c s)/((fiber r (r t)).card*(fiber c (c s)).card : ℝ)

theorem expanded_stochastic [DecidableEq ι] (r : ι → A) (c : ι → B) (pr : ∀ b,0<(fiber r b).card)
    (pc : ∀ b,0<(fiber c b).card) {a : A → B → ℝ} (nn : ∀ i j,0≤a i j)
    (row : ∀ i,∑ j,a i j=((fiber r i).card : ℝ)) (col : ∀ j,∑ i,a i j=((fiber c j).card : ℝ)) :
    expandSlots r c a ∈ doublyStochastic ℝ ι := by
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨fun t s => div_nonneg (nn _ _) (by positivity),?_,?_⟩
  · intro t
    have nz : ((fiber r (r t)).card : ℝ)≠0 := by exact_mod_cast (pr (r t)).ne'
    have sum := normalized_slot_sum c pc (fun j => a (r t) j/(fiber r (r t)).card)
    simp only [div_div,←Finset.sum_div,row,div_self nz] at sum
    exact sum
  · intro s
    have nz : ((fiber c (c s)).card : ℝ)≠0 := by exact_mod_cast (pc (c s)).ne'
    have sum := normalized_slot_sum r pr (fun i => a i (c s)/(fiber c (c s)).card)
    simp only [div_div,←Finset.sum_div,col,div_self nz] at sum
    simpa only [expandSlots,mul_comm] using sum

omit [Fintype A] [Fintype B] in
theorem group_expansion (r : ι → A) (c : ι → B) (pr : ∀ b,0<(fiber r b).card)
    (pc : ∀ b,0<(fiber c b).card) (a : A → B → ℝ) : grouping r c (expandSlots r c a)=a := by
  funext i j
  change grouped r c (expandSlots r c a) i j=_
  calc
    _ = ∑ _t ∈ fiber r i,∑ _s ∈ fiber c j,a i j/((fiber r i).card*(fiber c j).card : ℝ) := by
      apply sum_congr rfl
      intro t ht
      apply sum_congr rfl
      intro s hs
      simp only [expandSlots,mem_fiber.mp ht,mem_fiber.mp hs]
    _ = _ := by
      have hn : ((fiber r i).card : ℝ)≠0 := by exact_mod_cast (pr i).ne'
      have hm : ((fiber c j).card : ℝ)≠0 := by exact_mod_cast (pc j).ne'
      simp only [sum_const,nsmul_eq_mul]
      field_simp

end TransportationEhrhart
