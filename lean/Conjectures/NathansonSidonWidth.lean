import Conjectures.NathansonSidonLayers

/-! Integer diameter estimates before taking any limit in the size of the
ambient interval. Two lower-order errors fit inside one unit of slope. -/

namespace NathansonSidon

theorem middle_error {B H m T G Q t mid : ℕ} (pos : 0<B*G)
    (scale : m*T*H=G*Q) (large : 2*(B*G)≤t) (bounded : mid*t≤T) :
    2*(B*H*m*mid)≤Q := by
  have lift := Nat.mul_le_mul_left (B*H*m*mid) large
  have upper := Nat.mul_le_mul_left (B*H*m) bounded
  have result : (B*G)*(2*(B*H*m*mid))≤(B*G)*Q := calc
    _ = (B*H*m*mid)*(2*(B*G)) := by ring
    _ ≤ _ := lift
    _ = (B*H*m)*(mid*t) := by ring
    _ ≤ _ := upper
    _ = B*(m*T*H) := by ring
    _ = _ := by rw [scale]; ring
  exact Nat.le_of_mul_le_mul_left result pos

theorem place_width {A B G H m w T Q d x y e j : ℕ} (hw : 0<w) (hH : 0<H)
    (divides : w∣m) (scale : m*T*H=G*Q)
    (head : 2*(B*H*w*d)≤Q) (middle : 2*(B*H*m*e)≤Q)
    (step : x≤e+T*j) (slope : B*G*(y+j)<A*H*w) :
    B*(d+(m/w)*(x+T*y))≤A*Q := by
  have cancel : w*(m/w)=m := by rw [mul_comm,Nat.div_mul_cancel divides]
  have slack : B*H*w*d+B*H*m*e≤Q := by omega
  have bound : (H*w)*(B*(d+(m/w)*(x+T*y)))≤(H*w)*(A*Q) := calc
    _ = B*H*w*d+B*H*(w*(m/w))*x+B*((w*(m/w))*T*H)*y := by ring
    _ = B*H*w*d+B*H*m*x+B*(G*Q)*y := by rw [cancel,scale]
    _ ≤ B*H*w*d+B*H*m*(e+T*j)+B*(G*Q)*y := by gcongr
    _ = B*H*w*d+B*H*m*e+B*(m*T*H)*j+B*(G*Q)*y := by ring
    _ = (B*H*w*d+B*H*m*e)+(B*G*(y+j))*Q := by rw [scale]; ring
    _ ≤ Q+(B*G*(y+j))*Q := Nat.add_le_add_right slack _
    _ = (B*G*(y+j)+1)*Q := by ring
    _ ≤ (A*H*w)*Q := Nat.mul_le_mul_right _ slope
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left bound (Nat.mul_pos hH hw)

end NathansonSidon
