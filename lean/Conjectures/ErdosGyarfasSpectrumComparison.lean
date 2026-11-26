import Conjectures.ErdosGyarfasSpectrumTotals

/-! The slack in the mixed incidence count controls two square sums.
Cauchy–Schwarz then bounds the excess of the cross pairs over the low degrees. -/

namespace ErdosGyarfasSpectrum

variable {V : Type*} [DecidableEq V] {P X Y : Finset V} {lines : Finset (Finset V)}

def slack (a b r : ℤ) := a+b*(r-2)-a*b
private def leftWeight (a b : ℤ) := if 1≤a ∧ 2≤b then a else 0
private def rightWeight (a b : ℤ) := if 1≤a ∧ 2≤b then b-1 else 0

private theorem line_bounds {a b r : ℤ} (ha : 0≤a) (hb : 0≤b) (hr : 2≤r) (hab : a+b≤r) :
    let s := slack a b r; let u := leftWeight a b; let v := rightWeight a b
    0≤s ∧ 0≤u*v ∧ a*(b-1)≤u*v ∧ u^2≤a*(a-1)+s ∧ v^2≤s := by
  dsimp [slack,leftWeight,rightWeight]
  have ar : 0≤a*(a-1) := by
    by_cases az : a=0
    · simp [az]
    · exact mul_nonneg ha (by omega)
  have room := mul_nonneg hb (show 0≤r-a-b by omega)
  split_ifs with both
  · obtain ⟨a1,b2⟩ := both
    have prod := mul_nonneg ha (show 0≤b-1 by omega)
    have bmore := mul_nonneg hb (show 0≤b-2 by omega)
    refine ⟨?_,prod,le_rfl,?_,?_⟩ <;> nlinarith [sq_nonneg (b-1)]
  · have cases' : a=0 ∨ b=0 ∨ b=1 := by omega
    rcases cases' with az|bz|bo
    · subst a
      have h := mul_nonneg hb (show 0≤r-2 by omega)
      refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith
    · subst b
      refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg a]
    · subst b
      refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg a]

theorem total_slack (space : LinearOn P lines) (hX : X⊆P) (hY : Y⊆P) (disj : Disjoint X Y) :
    ∑ l∈lines, slack (amount X l) (amount Y l) l.card =
      lowTotal lines X+highTotal P lines Y-(X.card : ℤ)*Y.card := by
  simp only [slack,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [←low_total_lines,←high_total_lines space hY,mixed_pairs space hX hY disj]

theorem two_set_comparison (space : LinearOn P lines) (hX : X⊆P) (hY : Y⊆P) (disj : Disjoint X Y)
    {t : ℕ} (hx : X.card=t) (hy : Y.card=t) :
    let A := lowTotal lines X; let S := A+highTotal P lines Y-(t : ℤ)^2
    0≤S ∧ ∃ C : ℤ, 0≤C ∧ (t : ℤ)^2-A≤C ∧ C^2≤((t : ℤ)*(t-1)+S)*S := by
  let a (l : Finset V) := amount X l
  let b (l : Finset V) := amount Y l
  let s (l : Finset V) := slack (a l) (b l) l.card
  let u (l : Finset V) := leftWeight (a l) (b l)
  let v (l : Finset V) := rightWeight (a l) (b l)
  have facts (l : Finset V) (hl : l∈lines) :=
    line_bounds (a := a l) (b := b l) (r := l.card)
      (by dsimp [a]; rw [amount_eq]; exact_mod_cast Nat.zero_le _)
      (by dsimp [b]; rw [amount_eq]; exact_mod_cast Nat.zero_le _)
      (by exact_mod_cast (space.sizes l hl).1) (amounts_le_size X Y l disj)
  have total : ∑ l∈lines,s l=lowTotal lines X+highTotal P lines Y-(t : ℤ)^2 := by
    simpa only [s,a,b,hx,hy,pow_two] using total_slack space hX hY disj
  have internal : ∑ l∈lines,a l*(a l-1)=(t : ℤ)*(t-1) := by
    simpa only [a,hx] using internal_pairs space hX
  have cross : ∑ l∈lines,a l*b l=(t : ℤ)^2 := by
    simpa only [a,b,hx,hy,pow_two] using mixed_pairs space hX hY disj
  have totalA : ∑ l∈lines,a l = lowTotal lines X := (low_total_lines X lines).symm
  have left : ∑ l∈lines,(u l)^2 ≤ (t : ℤ)*(t-1)+∑ l∈lines,s l := by
    rw [←internal,←Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun l hl => (facts l hl).2.2.2.1
  have right : ∑ l∈lines,(v l)^2 ≤ ∑ l∈lines,s l :=
    Finset.sum_le_sum fun l hl => (facts l hl).2.2.2.2
  have nonneg : 0≤∑ l∈lines,s l := Finset.sum_nonneg fun l hl => (facts l hl).1
  dsimp only
  rw [←total]
  refine ⟨nonneg,∑ l∈lines,u l*v l,Finset.sum_nonneg (fun l hl => (facts l hl).2.1),?_,?_⟩
  · rw [←cross,←totalA,←Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro l hl
    have h := (facts l hl).2.2.1
    change a l*b l-a l ≤ leftWeight (a l) (b l)*rightWeight (a l) (b l)
    linarith
  · exact (Finset.sum_mul_sq_le_sq_mul_sq lines u v).trans
      (mul_le_mul left right (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by
        have h := Finset.sum_nonneg (s := lines) (fun l _ => sq_nonneg (u l))
        linarith))

end ErdosGyarfasSpectrum
