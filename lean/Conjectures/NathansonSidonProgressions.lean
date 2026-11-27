import Conjectures.NathansonSidonDigits
import Conjectures.NathansonSidonSystems

/-! Reflect each negative coefficient's digits. The resulting coordinate sets
are arithmetic progressions and their linear-form outputs are one full progression. -/

namespace NathansonSidon

def signedDigit {r : ℕ} (c : ℤ) (d : Fin r) : Fin r :=
  if c<0 then ⟨r-1-d.val,by have := d.isLt; omega⟩ else d

theorem signedDigit_involutive {r : ℕ} (c : ℤ) : Function.Involutive (@signedDigit r c) := by
  intro d
  by_cases neg : c<0
  · apply Fin.ext; simp [signedDigit,neg]; have := d.isLt; omega
  · simp [signedDigit,neg]

def coord {r : ℕ} (c : ℤ) (s : ℕ) (d : Fin r) : ℤ := 1+(s : ℤ)*(signedDigit c d).val

def shift (c : ℤ) (s r : ℕ) : ℤ := if c<0 then c*(1+s*(r-1 : ℕ)) else c

def coordinateSet (c : ℤ) (s r : ℕ) : Finset ℤ := Finset.univ.image (@coord r c s)

theorem coord_injective {r s : ℕ} (hs : 0<s) (c : ℤ) : Function.Injective (@coord r c s) := by
  intro x y eq
  apply (signedDigit_involutive c).injective
  apply Fin.ext
  have eq' := add_left_cancel (show 1+(s : ℤ)*(signedDigit c x).val=1+s*(signedDigit c y).val from eq)
  have nz : (s : ℤ)≠0 := by omega
  exact_mod_cast (mul_left_cancel₀ nz eq')

theorem coord_card {r s : ℕ} (hs : 0<s) (c : ℤ) : (coordinateSet c s r).card=r := by
  simp [coordinateSet,Finset.card_image_of_injective _ (coord_injective hs c)]

theorem contribution {r : ℕ} (c : ℤ) (s : ℕ) (d : Fin r) :
    c*coord c s d=shift c s r+(c.natAbs : ℤ)*s*d.val := by
  have hd := d.isLt
  by_cases neg : c<0
  · have abs := Int.ofNat_natAbs_of_nonpos (show c≤0 by omega)
    have rem : ((r-1-d.val : ℕ) : ℤ)=(r : ℤ)-1-d.val := by omega
    have rem' : ((r-1 : ℕ) : ℤ)=(r : ℤ)-1 := by omega
    simp only [coord,shift,signedDigit,ite_eq_left neg,rem,rem',abs]
    ring
  · simp [coord,shift,signedDigit,neg,Int.natAbs_of_nonneg (show 0≤c by omega)]
    ring

theorem positional_output {h r u : ℕ} (c : Fin h → ℤ) (s : Fin h → ℕ)
    (weights : ∀ i,(c i).natAbs*s i=u*r^i.val) (d : Fin h → Fin r) :
    output c (fun i => coord (c i) (s i) (d i)) =
      (∑ i,shift (c i) (s i) r)+(u : ℤ)*pack d := by
  simp only [output,contribution,Finset.sum_add_distrib,pack,Nat.cast_sum,Nat.cast_mul,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have eq : ((c i).natAbs : ℤ)*s i=(u : ℤ)*(r^i.val : ℕ) := by exact_mod_cast weights i
  rw [eq]; ring

theorem positional_feasible {h r u N : ℕ} (c : Fin h → ℤ) (s : Fin h → ℕ) (hu : 0<u)
    (hs : ∀ i,0<s i) (weights : ∀ i,(c i).natAbs*s i=u*r^i.val)
    (fits : ∀ i,1+s i*(r-1)≤N) : Feasible c N 1 r := by
  let A (i : Fin h) := coordinateSet (c i) (s i) r
  refine ⟨A,fun i => ⟨?_,coord_card (hs i) _⟩,?_⟩
  · intro a ha
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp ha
    have v := (signedDigit (c i) d).isLt
    have lim := Nat.mul_le_mul_left (s i) (show (signedDigit (c i) d).val≤r-1 by omega)
    have end' := fits i
    apply Finset.mem_Icc.mpr
    change 1≤1+(s i : ℤ)*(signedDigit (c i) d).val ∧ 1+(s i : ℤ)*(signedDigit (c i) d).val≤N
    constructor
    · have nz : 0 ≤ (s i : ℤ)*(signedDigit (c i) d).val := by positivity
      omega
    · exact_mod_cast (show 1+s i*(signedDigit (c i) d).val≤N by omega)
  · intro z
    apply representations_le_one_of_injective
    intro x hx y hy eq
    have reps {v : Fin h → ℤ} (mem : v∈Fintype.piFinset A) :
        ∃ d : Fin h → Fin r, (fun i => coord (c i) (s i) (d i))=v := by
      have ex (i : Fin h) := Finset.mem_image.mp (Fintype.mem_piFinset.mp mem i)
      choose d _ builds using ex
      exact ⟨d,funext builds⟩
    obtain ⟨dx,rfl⟩ := reps hx
    obtain ⟨dy,rfl⟩ := reps hy
    rw [positional_output c s weights,positional_output c s weights] at eq
    have nz : (u : ℤ)≠0 := by omega
    have code : pack dx=pack dy := by exact_mod_cast (mul_left_cancel₀ nz (add_left_cancel eq))
    by_cases hr : 0<r
    · rw [pack_injective hr code]
    · have eqd : dx=dy := funext fun i => False.elim (by have := (dx i).isLt; omega)
      rw [eqd]

theorem all_outputs {h r u : ℕ} (hr : 0<r) (c : Fin h → ℤ) (s : Fin h → ℕ)
    (weights : ∀ i,(c i).natAbs*s i=u*r^i.val) (n : ℕ) (hn : n<r^h) :
    ∃ x∈Fintype.piFinset (fun i => coordinateSet (c i) (s i) r),
      output c x=(∑ i,shift (c i) (s i) r)+(u : ℤ)*n := by
  obtain ⟨d,eq⟩ := pack_surjective hr h n hn
  refine ⟨fun i => coord (c i) (s i) (d i),Fintype.mem_piFinset.mpr (fun i =>
    Finset.mem_image_of_mem _ (Finset.mem_univ (d i))),?_⟩
  rw [positional_output c s weights,eq]

end NathansonSidon
