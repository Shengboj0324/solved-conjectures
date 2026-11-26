import Conjectures.NathansonSidonLayers
import Conjectures.NathansonSidonTopDigits

/-! Arithmetic for the sharp Sidon construction. Equal coordinate sizes
can be chosen on a fixed progression, and dyadic top digits approximate
the ratio of any two positive weights with strict room on both sides. -/

namespace NathansonSidon

theorem lowRadix_positive {h m : ℕ} (hm : 0<m) (b : Fin h → ℕ) (i : Fin h) :
    0<lowRadix m b i := by
  have pos : 0<(∏ i,lowRadix m b i)*lowGcd m b := by rwa [lowRadix_product]
  exact Nat.pos_of_dvd_of_pos (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    (Nat.pos_of_ne_zero (left_ne_zero_of_mul pos.ne'))

theorem lowRadix_le {h m : ℕ} (hm : 0<m) (b : Fin h → ℕ) (i : Fin h) :
    lowRadix m b i≤m := by
  apply Nat.le_of_dvd hm
  exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans
    ⟨lowGcd m b,(lowRadix_product m b).symm⟩

def layerPeriod {h : ℕ} (l p : Fin h → ℕ) : ℕ := ∏ i,l i*p i

def middleRadix {h : ℕ} (l p : Fin h → ℕ) (t : ℕ) (i : Fin h) : ℕ :=
  (layerPeriod l p/(l i*p i))*t

theorem layerPeriod_pos {h : ℕ} (l p : Fin h → ℕ) (hl : ∀ i,0<l i) (hp : ∀ i,0<p i) :
    0<layerPeriod l p := Finset.prod_pos fun i _ => Nat.mul_pos (hl i) (hp i)

theorem middleRadix_ge {h : ℕ} (l p : Fin h → ℕ) (hl : ∀ i,0<l i) (hp : ∀ i,0<p i)
    (t : ℕ) (i : Fin h) : t≤middleRadix l p t i := by
  have dvd : l i*p i∣layerPeriod l p := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have pos := Nat.div_pos (Nat.le_of_dvd (layerPeriod_pos l p hl hp) dvd) (Nat.mul_pos (hl i) (hp i))
  simpa only [middleRadix,one_mul] using Nat.mul_le_mul_right t (show 1≤layerPeriod l p/(l i*p i) from pos)

theorem middleRadix_size {h : ℕ} (l p : Fin h → ℕ) (t : ℕ) (i : Fin h) :
    l i*(middleRadix l p t i*p i)=layerPeriod l p*t := by
  have dvd : l i*p i∣layerPeriod l p := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  calc
    _ = (layerPeriod l p/(l i*p i)*(l i*p i))*t := by unfold middleRadix; ring
    _ = _ := by rw [Nat.div_mul_cancel dvd]

theorem mixedStride_full {h : ℕ} (r : Fin h → ℕ) (hr : ∀ i,0<r i) (i : Fin h) :
    mixedStride r i*r i≤∏ j,r j := by
  induction h with
  | zero => exact Fin.elim0 i
  | succ h ih =>
    rw [Fin.prod_univ_succ]
    refine Fin.cases ?_ (fun j => ?_) i
    · change 1*r 0≤r 0*∏ j : Fin h,r j.succ
      have pos : 0<∏ j : Fin h,r j.succ := Finset.prod_pos fun j _ => hr j.succ
      simpa only [one_mul,mul_one] using Nat.mul_le_mul_left (r 0) (show 1≤∏ j : Fin h,r j.succ from pos)
    · change (r 0*mixedStride (Fin.tail r) j)*r j.succ≤_
      simpa only [Fin.tail,mul_assoc] using Nat.mul_le_mul_left (r 0) (ih (Fin.tail r) (fun j => hr j.succ) j)

theorem dyadic_allocation {u v G A B : ℕ} (hu : 0<u) (hv : 0<v)
    (slope : B*G<A*(u+v)) :
    ∃ J D : ℕ, D<2^J ∧ B*G*D<A*(2^J)*u ∧ B*G*(2^J-D)<A*(2^J)*v := by
  let s := u+v
  let J := B*G*s+1
  let H := 2^J
  have hs : 0<s := by dsimp [s]; omega
  have hH : B*G*s<H := lt_trans (by dsimp [J]; omega : B*G*s<J) (Nat.lt_two_pow_self)
  have Hpos : 0<H := by dsimp [H]; positivity
  let D := H*u/s
  let rem := H*u%s
  have split : s*D+rem=H*u := Nat.div_add_mod (H*u) s
  have rlt : rem<s := Nat.mod_lt _ hs
  have up : D<H := (Nat.div_lt_iff_lt_mul hs).2 (Nat.mul_lt_mul_of_pos_left (by dsimp [s]; omega) Hpos)
  refine ⟨J,D,up,?_,?_⟩
  · have first : B*G*(s*D)≤B*G*(H*u) := Nat.mul_le_mul_left _ (by omega)
    have strict := Nat.mul_lt_mul_of_pos_right (show B*G<A*s from slope) (Nat.mul_pos Hpos hu)
    apply Nat.lt_of_mul_lt_mul_left (a := s)
    calc
      s*(B*G*D) = B*G*(s*D) := by ring
      _ ≤ _ := first
      _ < _ := strict
      _ = s*(A*H*u) := by ring
  · have deficit : s*(H-D)=H*v+rem := by
      rw [Nat.mul_sub,(show s*H=H*u+H*v by dsimp [s]; ring)]
      omega
    have re : B*G*rem<H*v :=
      (Nat.mul_le_mul_left (B*G) rlt.le).trans_lt (hH.trans_le (Nat.le_mul_of_pos_right _ hv))
    have room : (B*G+1)*(H*v)≤(A*s)*(H*v) := Nat.mul_le_mul_right _ slope
    apply Nat.lt_of_mul_lt_mul_left (a := s)
    calc
      s*(B*G*(H-D)) = B*G*(H*v)+B*G*rem := by rw [←Nat.mul_add,←deficit]; ring
      _ < (B*G+1)*(H*v) := by rw [Nat.add_mul,Nat.one_mul]; omega
      _ ≤ _ := room
      _ = s*(A*H*v) := by ring

end NathansonSidon
