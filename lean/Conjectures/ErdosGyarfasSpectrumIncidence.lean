import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact incidence counts for finite linear spaces. Every pair of distinct
points is on one line. The lines are finite subsets of the point set. -/

namespace ErdosGyarfasSpectrum

variable {V : Type*} [DecidableEq V]

structure LinearOn (P : Finset V) (lines : Finset (Finset V)) : Prop where
  order : 3 ≤ P.card
  subsets : ∀ l∈lines, l⊆P
  sizes : ∀ l∈lines, 2 ≤ l.card ∧ l.card<P.card
  pair : ∀ p∈P, ∀ q∈P, p≠q → ∃! l, l∈lines ∧ p∈l ∧ q∈l

def hit (p : V) (l : Finset V) : ℤ := if p∈l then 1 else 0

def amount (X l : Finset V) : ℤ := ∑ p∈X, hit p l

def degree (lines : Finset (Finset V)) (p : V) : ℕ := (lines.filter (p∈·)).card

theorem amount_eq (X l : Finset V) : amount X l=((X∩l).card : ℤ) := by
  simp [amount,hit]

theorem degree_eq (lines : Finset (Finset V)) (p : V) : (degree lines p : ℤ)=∑ l∈lines, hit p l := by
  simp [degree,hit]

theorem amount_erase {p : V} {X : Finset V} (hp : p∈X) (l : Finset V) :
    amount (X.erase p) l=amount X l-hit p l := by
  have h := Finset.sum_erase_add _ (fun q => hit q l) hp
  unfold amount
  omega

theorem pair_sum {P : Finset V} {lines : Finset (Finset V)} (space : LinearOn P lines)
    {p q : V} (hp : p∈P) (hq : q∈P) (hne : p≠q) :
    ∑ l∈lines, hit p l*hit q l=1 := by
  obtain ⟨l,⟨hl,hp',hq'⟩,uniq⟩ := space.pair p hp q hq hne
  rw [Finset.sum_eq_single l]
  · simp [hit,hp',hq']
  · intro k hk ne
    by_cases a : p∈k <;> by_cases b : q∈k <;> simp_all [hit]
  · exact fun h => (h hl).elim

theorem partners {P X : Finset V} {lines : Finset (Finset V)} (space : LinearOn P lines)
    {p : V} (hp : p∈P) (hX : X⊆P) (notin : p∉X) :
    ∑ l∈lines, hit p l*amount X l=(X.card : ℤ) := by
  simp only [amount,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ _q∈X, (1 : ℤ) := Finset.sum_congr rfl fun q hq =>
      pair_sum space hp (hX hq) (fun e => notin (e ▸ hq))
    _ = _ := by simp

theorem partners_inside {P X : Finset V} {lines : Finset (Finset V)} (space : LinearOn P lines)
    (hX : X⊆P) {p : V} (hp : p∈X) :
    ∑ l∈lines, hit p l*(amount X l-1)=(X.card : ℤ)-1 := by
  calc
    _ = ∑ l∈lines, hit p l*amount (X.erase p) l := by
      apply Finset.sum_congr rfl
      intro l _
      rw [amount_erase hp]
      by_cases mem : p∈l <;> simp [hit,mem]
    _ = ((X.erase p).card : ℤ) := partners space (hX hp) (fun _ h => hX (Finset.mem_of_mem_erase h))
      (Finset.notMem_erase _ _)
    _ = _ := by
      have n := Finset.card_erase_add_one hp
      omega

theorem sum_incidences (X : Finset V) (lines : Finset (Finset V)) (w : Finset V → ℤ) :
    ∑ l∈lines, amount X l*w l=∑ p∈X, ∑ l∈lines, hit p l*w l := by
  simp only [amount,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem mixed_pairs {P X Y : Finset V} {lines : Finset (Finset V)} (space : LinearOn P lines)
    (hX : X⊆P) (hY : Y⊆P) (disj : Disjoint X Y) :
    ∑ l∈lines, amount X l*amount Y l=(X.card : ℤ)*Y.card := by
  rw [sum_incidences]
  calc
    _ = ∑ _p∈X,(Y.card : ℤ) := Finset.sum_congr rfl fun p hp =>
      partners space (hX hp) hY (fun h => Finset.disjoint_left.mp disj hp h)
    _ = _ := by simp

theorem internal_pairs {P X : Finset V} {lines : Finset (Finset V)} (space : LinearOn P lines)
    (hX : X⊆P) : ∑ l∈lines, amount X l*(amount X l-1)=(X.card : ℤ)*(X.card-1) := by
  rw [sum_incidences]
  calc
    _ = ∑ _p∈X,((X.card : ℤ)-1) := Finset.sum_congr rfl fun _ hp => partners_inside space hX hp
    _ = _ := by simp; ring

end ErdosGyarfasSpectrum
