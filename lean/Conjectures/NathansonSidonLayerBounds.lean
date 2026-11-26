import Conjectures.NathansonSidonAllocation
import Conjectures.NathansonSidonWidth

/-! A uniform bound on every actual coordinate of a three-level Sidon
system, including the full middle digit of its last coordinate. -/

namespace NathansonSidon

theorem weighted_layers_fit {h m H A B G Q t N : ℕ} (hm : 0<m) (hH : 0<H) (hB : 0<B) (hG : 0<G)
    (hN : 0<N) (b r p : Fin h → ℕ) (bw : ∀ i,0<b i) (divides : ∀ i,b i∣m)
    (rr : ∀ i,0<r i) (last : Fin h) (maxi : ∀ i,i≤last) (rt : t≤r last)
    (upper : ∀ i,Fin (p i) → ℕ) (scale : m*(∏ i,r i)*H=G*Q)
    (large : 2*(B*G)≤t) (head : 2*(B*H*m^2)≤Q) (budget : A*Q≤B*(N-1))
    (caps : ∀ i d,B*G*(upper i d+(if i=last then 1 else 0))<A*H*b i)
    (i : Fin h) (d : LayerDigit (lowRadix m b i) (r i) (p i)) :
    layeredPlace m b r p upper i d<N := by
  let mid := mixedStride r i*d.2.1.val
  have bi := Nat.le_of_dvd hm (divides i)
  have di := d.1.isLt.le.trans (lowRadix_le hm b i)
  have err : 2*(B*H*b i*d.1.val)≤Q := calc
    _ = 2*((B*H)*(b i*d.1.val)) := by ring
    _ ≤ 2*((B*H)*(m*m)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (Nat.mul_le_mul bi di))
    _ ≤ Q := by simpa only [sq] using head
  have midBound : mid≤mixedStride r i*r i := Nat.mul_le_mul_left _ d.2.1.isLt.le
  suffices bound : B*layeredPlace m b r p upper i d≤A*Q by
    have := Nat.le_of_mul_le_mul_left (bound.trans budget) hB
    omega
  by_cases endp : i=last
  · have topLimit := caps i d.2.2
    rw [ite_eq_left endp] at topLimit
    apply place_width (Q := Q) (T := ∏ j,r j) (e := 0) (j := 1) (bw i) hH (divides i) scale err
      (by simp) _ topLimit
    simpa only [zero_add,mul_one] using midBound.trans (mixedStride_full r rr i)
  · have step : mid*t≤∏ j,r j := (Nat.mul_le_mul midBound rt).trans
      (mixedStride_before r rr i last (lt_of_le_of_ne (maxi i) endp))
    have tailErr := middle_error (Nat.mul_pos hB hG) scale large step
    have topLimit := caps i d.2.2
    rw [ite_eq_right endp] at topLimit
    exact place_width (e := mid) (j := 0) (bw i) hH (divides i) scale err tailErr (by simp [mid]) topLimit

end NathansonSidon
