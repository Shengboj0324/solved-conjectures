import Conjectures.NathansonSidonLowDigits
import Conjectures.NathansonSidonMixedRadix
import Conjectures.NathansonSidonSignedSets

/-! A low residue, a mixed-radix digit and an upper digit form each
coordinate. The weighted sum recovers all three levels uniquely. -/

namespace NathansonSidon

abbrev LayerDigit (l r p : ℕ) := Fin l × Fin r × Fin p

def layeredPlace {h : ℕ} (m : ℕ) (b r p : Fin h → ℕ)
    (upper : ∀ i,Fin (p i) → ℕ) (i : Fin h)
    (d : LayerDigit (lowRadix m b i) (r i) (p i)) : ℕ :=
  d.1.val+(m/b i)*(mixedStride r i*d.2.1.val+(∏ j,r j)*upper i d.2.2)

theorem layered_sum {h m : ℕ} (b r p : Fin h → ℕ) (hb : ∀ i,b i∣m)
    (upper : ∀ i,Fin (p i) → ℕ) (d : ∀ i,LayerDigit (lowRadix m b i) (r i) (p i)) :
    (∑ i,b i*layeredPlace m b r p upper i (d i))=
      lowOutput b (fun i => (d i).1.val)+m*(mixedPack r (fun i => (d i).2.1.val)+
      (∏ j,r j)*∑ i,upper i (d i).2.2) := by
  have scale (i : Fin h) : b i*(m/b i)=m := by
    rw [Nat.mul_comm,Nat.div_mul_cancel (hb i)]
  simp only [layeredPlace,Nat.mul_add,←Nat.mul_assoc,scale,lowOutput,mixedPack_eq_sum,
    Finset.sum_add_distrib,Finset.mul_sum]

theorem layered_unique {h m : ℕ} (hm : 0<m) (b r p : Fin h → ℕ)
    (hb : ∀ i,b i∣m) (hr : ∀ i,0<r i) (upper : ∀ i,Fin (p i) → ℕ)
    (hu : Function.Injective (fun d : ∀ i,Fin (p i) => ∑ i,upper i (d i))) :
    Function.Injective (fun d : ∀ i,LayerDigit (lowRadix m b i) (r i) (p i) =>
      ∑ i,b i*layeredPlace m b r p upper i (d i)) := by
  intro x y eq
  change (∑ i,b i*layeredPlace m b r p upper i (x i))=
    ∑ i,b i*layeredPlace m b r p upper i (y i) at eq
  rw [layered_sum b r p hb upper x,layered_sum b r p hb upper y] at eq
  have lowEq := congrArg (fun t => t%m) eq
  simp only [Nat.add_mul_mod_self_left] at lowEq
  have low := lowDigits_unique hm b (fun i => (x i).1.val) (fun i => (y i).1.val)
    (fun i => (x i).1.isLt) (fun i => (y i).1.isLt) lowEq
  rw [low] at eq
  have midTop := Nat.eq_of_mul_eq_mul_left hm (Nat.add_left_cancel eq)
  have midEq := congrArg (fun t => t%(∏ i,r i)) midTop
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (mixedPack_lt r _ fun i => (x i).2.1.isLt),
    Nat.mod_eq_of_lt (mixedPack_lt r _ fun i => (y i).2.1.isLt)] at midEq
  have mid := mixedPack_unique r (fun i => (x i).2.1.val) (fun i => (y i).2.1.val)
    (fun i => (x i).2.1.isLt) (fun i => (y i).2.1.isLt) midEq
  rw [midEq] at midTop
  have top := hu (Nat.eq_of_mul_eq_mul_left (Finset.prod_pos fun i _ => hr i) (Nat.add_left_cancel midTop))
  funext i
  exact Prod.ext (Fin.ext (congrFun low i)) (Prod.ext (Fin.ext (congrFun mid i)) (congrFun top i))

private theorem coordinate_unique {h : ℕ} {α : Fin h → Type*} [∀ i,Nonempty (α i)]
    (b : Fin h → ℕ) (f : ∀ i,α i → ℕ)
    (total : Function.Injective (fun d : ∀ i,α i => ∑ i,b i*f i (d i))) (i : Fin h) :
    Function.Injective (f i) := by
  classical
  intro x y eq
  let d : ∀ i,α i := fun _ => Classical.choice inferInstance
  have values (j : Fin h) : f j (Function.update d i x j)=f j (Function.update d i y j) := by
    by_cases hji : j=i
    · subst j; simpa using eq
    · simp [Function.update_of_ne hji]
  have same := total (a₁ := Function.update d i x) (a₂ := Function.update d i y)
    (Finset.sum_congr rfl fun j _ => congrArg (b j*·) (values j))
  simpa using congrFun same i

theorem layered_feasible {h m q N : ℕ} (hm : 0<m) (c : Fin h → ℤ) (r p : Fin h → ℕ)
    (hb : ∀ i,(c i).natAbs∣m) (hr : ∀ i,0<r i) (hq : 0<q)
    (size : ∀ i,lowRadix m (fun j => (c j).natAbs) i*(r i*p i)=q)
    (upper : ∀ i,Fin (p i) → ℕ)
    (hu : Function.Injective (fun d : ∀ i,Fin (p i) => ∑ i,upper i (d i)))
    (fits : ∀ i d,layeredPlace m (fun j => (c j).natAbs) r p upper i d<N) :
    Feasible c N 1 q := by
  let b := fun i => (c i).natAbs
  let f := layeredPlace m b r p upper
  have total := layered_unique hm b r p hb hr upper hu
  have sz (i : Fin h) : Fintype.card (LayerDigit (lowRadix m b i) (r i) (p i))=q := by
    simpa only [LayerDigit,Fintype.card_prod,Fintype.card_fin] using size i
  let (i : Fin h) : Nonempty (LayerDigit (lowRadix m b i) (r i) (p i)) :=
    Fintype.card_pos_iff.mp ((sz i).symm ▸ hq)
  exact weighted_sets_feasible c f sz fits (coordinate_unique b f total) total

theorem radix_product_identity {h m q : ℕ} (b r p : Fin h → ℕ)
    (size : ∀ i,lowRadix m b i*(r i*p i)=q) :
    m*(∏ i,r i)*(∏ i,p i)=lowGcd m b*q^h := by
  have prod := Finset.prod_congr (s₁ := (Finset.univ : Finset (Fin h))) rfl (fun i _ => size i)
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at prod
  calc
    m*(∏ i,r i)*(∏ i,p i) =
        ((∏ i,lowRadix m b i)*lowGcd m b)*(∏ i,r i)*(∏ i,p i) :=
      congrArg (fun t => t*(∏ i,r i)*(∏ i,p i)) (lowRadix_product m b).symm
    _ = lowGcd m b*((∏ i,lowRadix m b i)*((∏ i,r i)*(∏ i,p i))) := by ring
    _ = _ := congrArg (lowGcd m b*·) prod

end NathansonSidon
