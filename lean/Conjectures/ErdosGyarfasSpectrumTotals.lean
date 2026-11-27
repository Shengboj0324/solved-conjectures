import Conjectures.ErdosGyarfasSpectrumIncidence
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The sum of the low degrees and the sum of the high deficits both have
exact descriptions as weighted sums over lines. -/

namespace ErdosGyarfasSpectrum

variable {V : Type*} [DecidableEq V] {P X Y : Finset V} {lines : Finset (Finset V)}

def lowTotal (lines : Finset (Finset V)) (X : Finset V) : ℤ := ∑ p∈X,(degree lines p : ℤ)

def highTotal (P : Finset V) (lines : Finset (Finset V)) (Y : Finset V) : ℤ :=
  ∑ p∈Y, ((P.card : ℤ)-1-degree lines p)

theorem ambient_amount (h : LinearOn P lines) {l : Finset V} (hl : l∈lines) :
    amount P l=(l.card : ℤ) := by
  rw [amount_eq,Finset.inter_eq_right.mpr (h.subsets _ hl)]

theorem low_total_lines (X : Finset V) (lines : Finset (Finset V)) :
    lowTotal lines X=∑ l∈lines,amount X l := by
  simp only [lowTotal,degree_eq,amount]
  rw [Finset.sum_comm]

theorem point_deficit (space : LinearOn P lines) {p : V} (hp : p∈P) :
    (P.card : ℤ)-1-degree lines p=∑ l∈lines,hit p l*((l.card : ℤ)-2) := by
  rw [degree_eq,←partners_inside space (fun _ h => h) hp,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [ambient_amount space hl]
  ring

theorem high_total_lines (space : LinearOn P lines) (hY : Y⊆P) :
    highTotal P lines Y=∑ l∈lines,amount Y l*((l.card : ℤ)-2) := by
  rw [sum_incidences]
  exact Finset.sum_congr rfl fun _ hp => point_deficit space (hY hp)

theorem degree_lt (space : LinearOn P lines) {p : V} (hp : p∈P) : degree lines p<P.card := by
  have pos : 0 ≤ ∑ l∈lines,hit p l*((l.card : ℤ)-2) := by
    apply Finset.sum_nonneg
    intro l hl
    have s := (space.sizes l hl).1
    by_cases mem : p∈l
    · simp [hit,mem]; omega
    · simp [hit,mem]
  rw [←point_deficit space hp] at pos
  omega

theorem degree_pos (space : LinearOn P lines) {p : V} (hp : p∈P) : 0<degree lines p := by
  have n := space.order
  have c := Finset.card_erase_add_one hp
  obtain ⟨q,hq⟩ := Finset.card_pos.mp (show 0<(P.erase p).card by omega)
  obtain ⟨hne,hq'⟩ := Finset.mem_erase.mp hq
  obtain ⟨l,⟨hl,mem,_⟩,_⟩ := space.pair p hp q hq' hne.symm
  exact Finset.card_pos.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,mem⟩⟩

theorem amounts_le_size (X Y l : Finset V) (disj : Disjoint X Y) :
    amount X l+amount Y l ≤ (l.card : ℤ) := by
  have d : Disjoint (X∩l) (Y∩l) := Finset.disjoint_left.mpr fun _ hx hy =>
    Finset.disjoint_left.mp disj (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hy).1
  have inc : (X∩l) ∪ (Y∩l) ⊆ l := by
    intro p hp
    rcases Finset.mem_union.mp hp with hx|hy
    · exact (Finset.mem_inter.mp hx).2
    · exact (Finset.mem_inter.mp hy).2
  have lim := Finset.card_le_card inc
  rw [Finset.card_union_of_disjoint d] at lim
  rw [amount_eq,amount_eq]
  omega

end ErdosGyarfasSpectrum
