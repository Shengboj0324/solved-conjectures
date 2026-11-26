import Conjectures.NathansonSidonLayerBounds
import Conjectures.NathansonSidonSteps

/-! Every strictly smaller rational slope is realized by genuine coordinate
sets at all sufficiently large multiples of one fixed common size. -/

namespace NathansonSidon

theorem sharp_progression {h A B : ℕ} (hh : 0<h) (hA : 0<A) (hB : 0<B)
    (c : Fin h → ℤ) (nz : ∀ i,c i≠0) (a j : Fin h) (aj : a≠j) (last : ∀ i,i≤j)
    (slope : B*coefficientGcd c<A*((c a).natAbs+(c j).natAbs)) :
    ∃ C : ℕ, 0<C ∧ ∃ t₀ : ℕ, ∀ t≥t₀, ∀ N : ℕ, 0<N →
      A*(C*t)^h≤B*(N-1) → Feasible c N 1 (C*t) := by
  let b := fun i => (c i).natAbs
  let m := period c
  let G := coefficientGcd c
  have bw (i : Fin h) : 0<b i := Int.natAbs_pos.mpr (nz i)
  have hm : 0<m := period_pos c nz
  have hG : 0<G := coefficientGcd_pos hh c nz
  have divs (i : Fin h) : b i∣m := Finset.dvd_lcm (Finset.mem_univ i)
  have common : G∣m := (gcd_dvd_weight c a).trans (divs a)
  have gcdEq : lowGcd m b=G := (lowGcd_eq_gcd b).trans (Nat.gcd_eq_right common)
  obtain ⟨J,D,below,lc,rc⟩ := dyadic_allocation (bw a) (bw j) slope
  let H := 2^J
  have hH : 0<H := pow_pos (by decide) _
  obtain ⟨s,prod,lmax,rmax⟩ := balanced_binary_split J D below
  have sprod : 0<s.leftCount*s.rightCount := prod ▸ hH
  have ls : 0<s.leftCount := Nat.pos_of_ne_zero (left_ne_zero_of_mul sprod.ne')
  have rs : 0<s.rightCount := Nat.pos_of_ne_zero (right_ne_zero_of_mul sprod.ne')
  let p := topCount s a j
  let l := lowRadix m b
  have pp (i : Fin h) : 0<p i := by
    dsimp [p,topCount]
    split_ifs <;> positivity
  have lp := lowRadix_positive hm b
  let C := layerPeriod l p
  have cp : 0<C := layerPeriod_pos l p lp pp
  refine ⟨C,cp,2*(B*G)+2*(B*H*m^2)+1,?_⟩
  intro t ht N hN budget
  let r := middleRadix l p t
  have htpos : 0<t := by omega
  have rge (i : Fin h) : t≤r i := middleRadix_ge l p lp pp t i
  have rpos (i : Fin h) : 0<r i := htpos.trans_le (rge i)
  have sz (i : Fin h) : l i*(r i*p i)=C*t := middleRadix_size l p t i
  have scale := radix_product_identity b r p sz
  change m*(∏ i,r i)*(∏ i,topCount s a j i)=lowGcd m b*(C*t)^h at scale
  rw [topCount_product,prod,gcdEq] at scale
  have room : 2*(B*H*m^2)≤(C*t)^h := calc
    _ ≤ t := by omega
    _ ≤ C*t := by simpa only [one_mul] using Nat.mul_le_mul_right t (show 1≤C from cp)
    _ ≤ _ := Nat.le_pow hh
  apply layered_feasible hm c r p divs rpos (Nat.mul_pos cp htpos) sz (topDigit s a j) (topDigit_unique s a j aj)
  apply weighted_layers_fit hm hH hB hG hN b r p bw divs rpos j last (rge j) _ scale (by omega) room budget
  intro i d
  have top := topDigit_bounds s a j aj i d
  by_cases ia : i=a
  · subst i
    have td : topDigit s a j a d≤D := by simpa [aj,lmax] using top
    simpa [aj] using (Nat.mul_le_mul_left (B*G) td).trans_lt lc
  by_cases ij : i=j
  · subst i
    have td : topDigit s a j j d≤2^J-1-D := by simpa [ia,rmax] using top
    have cap : topDigit s a j j d+1≤2^J-D := by omega
    simpa using (Nat.mul_le_mul_left (B*G) cap).trans_lt rc
  · simp only [ite_eq_right ia,ite_eq_right ij] at top
    simp only [ite_eq_right ij,add_zero,Nat.eq_zero_of_le_zero top,mul_zero]
    exact Nat.mul_pos (Nat.mul_pos hA hH) (bw i)

end NathansonSidon
