import Conjectures.NathansonSidonGcd
import Mathlib.Tactic

/-! Zero-based nonnegative digit sets give actual signed, one-based Sidon
systems. The normalized diameter bounds their size at every positive order. -/

namespace NathansonSidon

def signedPlace (c : ℤ) (N x : ℕ) : ℤ :=
  if c<0 then (N : ℤ)-x else (x : ℤ)+1

theorem signedPlace_injective (c : ℤ) (N : ℕ) : Function.Injective (signedPlace c N) := by
  intro x y eq
  by_cases h : c<0 <;> simp [signedPlace,h] at eq <;> omega

theorem signedPlace_bounds {x N : ℕ} (c : ℤ) (hx : x<N) :
    signedPlace c N x∈Finset.Icc 1 (N : ℤ) := by
  rw [Finset.mem_Icc]
  by_cases h : c<0 <;> simp [signedPlace,h] <;> omega

theorem signedPlace_weight (c : ℤ) (N x : ℕ) :
    c*signedPlace c N x=((c.natAbs*x : ℕ) : ℤ)+c*(if c<0 then (N : ℤ) else 1) := by
  by_cases h : c<0
  · simp only [signedPlace,ite_eq_left h,Nat.cast_mul,Int.natCast_natAbs,abs_of_neg h]
    ring
  · simp only [signedPlace,ite_eq_right h,Nat.cast_mul,Int.natCast_natAbs,abs_of_nonneg (le_of_not_gt h)]
    ring

theorem weighted_sets_feasible {h q N : ℕ} (c : Fin h → ℤ) {α : Fin h → Type*}
    [∀ i,Fintype (α i)] (f : ∀ i,α i → ℕ)
    (sizes : ∀ i,Fintype.card (α i)=q) (fits : ∀ i x,f i x<N)
    (coords : ∀ i,Function.Injective (f i))
    (unique : Function.Injective (fun x : ∀ i,α i => ∑ i,(c i).natAbs*f i (x i))) :
    Feasible c N 1 q := by
  classical
  let m (i : Fin h) (x : α i) := signedPlace (c i) N (f i x)
  let A (i : Fin h) := Finset.univ.image (m i)
  have liftTuple (x : Fin h → ℤ) (hx : x∈Fintype.piFinset A) :
      ∃ d : ∀ i,α i, (fun i => m i (d i))=x := by
    have hpre (i : Fin h) : ∃ d : α i,m i d=x i := by
      obtain ⟨d,_,he⟩ := Finset.mem_image.mp (Fintype.mem_piFinset.mp hx i)
      exact ⟨d,he⟩
    choose d hd using hpre
    exact ⟨d,funext hd⟩
  have offset (x : ∀ i,α i) : output c (fun i => m i (x i)) =
      ((∑ i,(c i).natAbs*f i (x i) : ℕ) : ℤ)+
      ∑ i,c i*(if c i<0 then (N : ℤ) else 1) := by
    simp only [output,m,signedPlace_weight,Finset.sum_add_distrib,Nat.cast_sum]
  refine ⟨A,fun i => ⟨?_,?_⟩,representations_le_one_of_injective c A ?_⟩
  · intro x hx
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hx
    exact signedPlace_bounds _ (fits i d)
  · have hi : Function.Injective (m i) := (signedPlace_injective _ _).comp (coords i)
    simpa only [A,Finset.card_image_of_injective _ hi,Finset.card_univ] using sizes i
  · intro x hx y hy eq
    obtain ⟨d,rfl⟩ := liftTuple x hx
    obtain ⟨e,rfl⟩ := liftTuple y hy
    rw [offset,offset] at eq
    have hde := unique (Nat.cast_injective (add_right_cancel eq : (_ : ℤ)=_))
    rw [hde]

theorem power_ratio_upper {h N g : ℕ} (hh : 0<h) (hN : 0<N) (c : Fin h → ℤ)
    (nz : ∀ i,c i≠0) :
    (extremal c N g : ℝ)^h/(N : ℝ)≤(g : ℝ)*(coefficientSum c/coefficientGcd c : ℕ) := by
  let k := coefficientSum c/coefficientGcd c
  let i : Fin h := ⟨0,hh⟩
  have someWeight := Int.natAbs_pos.mpr (nz i)
  have dpos := coefficientGcd_pos hh c nz
  have dle := (Nat.le_of_dvd someWeight (gcd_dvd_weight c i)).trans
    (Finset.single_le_sum (f := fun j => (c j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have kpos : 0<k := Nat.div_pos dle dpos
  have bound := normalized_diameter hh nz (extremal_feasible hh c N g)
  have count : (extremal c N g)^h≤g*k*N := by
    refine bound.trans ?_
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    change k*t+1≤k*(t+1)
    rw [Nat.mul_add,Nat.mul_one]
    omega
  apply (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ)<N)).mpr
  exact_mod_cast count

end NathansonSidon
