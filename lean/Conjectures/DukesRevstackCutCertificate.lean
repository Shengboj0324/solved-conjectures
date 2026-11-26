import Conjectures.DukesRevstackRows
import Conjectures.DukesRevstackBrackets
import Conjectures.DukesRevstackEnumeration

/-! Exact integer predicates connect dyadic separating intervals to strict
interlacing for the literal revstack descent polynomials. -/

open Polynomial

namespace DukesRevstack

abbrev Cut := ℤ × ℕ

def cutAt (cuts : Array Cut) (i : ℕ) : Cut := cuts[i]?.getD (0,1)

noncomputable def cutReal (c : Cut) : ℝ := (c.1 : ℝ)/(c.2 : ℝ)

abbrev cutLT (a b : Cut) : Prop := a.1*(b.2 : ℤ)<b.1*(a.2 : ℤ)

abbrev signChange (co : List ℤ) (a b : Cut) : Prop :=
  let l := (scaledValue a.1 a.2 co).1
  let r := (scaledValue b.1 b.2 co).1
  (l<0 ∧ 0<r) ∨ (0<l ∧ r<0)

abbrev oldBracket (p : List ℤ) (cs : Array Cut) (i : ℕ) :=
  signChange p (cutAt cs (2*i+1)) (cutAt cs (2*i+2))

abbrev newBracket (q : List ℤ) (cs : Array Cut) (i : ℕ) :=
  signChange q (cutAt cs (2*i)) (cutAt cs (2*i+1))

abbrev certifiedCuts (d : ℕ) (p q : List ℤ) (cs : Array Cut) : Prop :=
  cs.size=2*d+2 ∧ (∀ i : Fin (2*d+2),0<(cutAt cs i.val).2) ∧
  (∀ i : Fin (2*d+1),cutLT (cutAt cs i.val) (cutAt cs (i.val+1))) ∧
  (cutAt cs (2*d+1)).1≤0 ∧
  (∀ i : Fin d,oldBracket p cs i.val) ∧ (∀ i : Fin (d+1),newBracket q cs i.val)

private theorem real_cut_lt {a b : Cut} (ha : 0<a.2) (hb : 0<b.2) (hab : cutLT a b) :
    cutReal a<cutReal b := by
  apply (div_lt_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hb)).mpr
  exact_mod_cast hab

private theorem eval_opposite {p : List ℤ} {a b : Cut} (ha : 0<a.2) (hb : 0<b.2)
    (h : signChange p a b) :
    (polynomialOfRow p).eval (cutReal a)*(polynomialOfRow p).eval (cutReal b)<0 := by
  apply opposite_signs_of_scaled p a.1 (a.2 : ℤ) b.1 (b.2 : ℤ)
    (by exact_mod_cast ha) (by exact_mod_cast hb)
  rcases h with ⟨l,r⟩|⟨l,r⟩
  · exact mul_neg_of_neg_of_pos l r
  · exact mul_neg_of_pos_of_neg l r

def literalInterlaces (n : ℕ) : Prop :=
  ∃ a : Fin (n-1) → ℝ,∃ b : Fin (n-1+1) → ℝ,
    StrictMono a ∧ StrictMono b ∧ (∀ i,a i<0) ∧ (∀ i,b i<0) ∧
    (∀ i : Fin (n-1),b i.castSucc<a i ∧ a i<b i.succ) ∧
    revstackDescentPolynomial (R := ℝ) n (n-2)=X*∏ i,(X-C (a i)) ∧
    revstackDescentPolynomial (R := ℝ) (n+1) (n+1-2)=X*∏ i,(X-C (b i))

theorem literal_interlacing_of_certificate (n : ℕ) (hn : 3≤n) (p q : List ℤ) (cs : Array Cut)
    (ep : p=reducedRow n) (eq : q=reducedRow (n+1)) (valid : certifiedCuts (n-1) p q cs) :
    literalInterlaces n := by
  let d := n-1
  obtain ⟨_,positive,adjacent,last,oldSigns,newSigns⟩ := valid
  let val := fun i => cutReal (cutAt cs i)
  have pos (i : ℕ) (hi : i≤2*d+1) : 0<(cutAt cs i).2 := positive ⟨i,by dsimp [d] at hi; omega⟩
  have mono : StrictMono (fun i : Fin (2*d+2) => val i.val) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact real_cut_lt (pos _ (by omega)) (pos _ (by omega)) (adjacent i)
  have inc (i j : ℕ) (lt : i<j) (hi : j≤2*d+1) : val i<val j :=
    mono (a := ⟨i,by omega⟩) (b := ⟨j,by omega⟩) lt
  have endp : val (2*d+1)≤0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast last) (Nat.cast_nonneg _)
  have P : polynomialOfRow p = reducedRevstack (R := ℝ) n := ep ▸ reduced_row_correct n hn
  have Q : polynomialOfRow q = reducedRevstack (R := ℝ) (n+1) := eq ▸ reduced_row_correct _ (by omega)
  have hp : IsMonicOfDegree (polynomialOfRow p) d := P ▸ reducedRevstack_monic_degree _ hn
  have hq : IsMonicOfDegree (polynomialOfRow q) (d+1) := by
    rw [Q,show d+1=n+1-1 by dsimp [d]; omega]
    exact reducedRevstack_monic_degree _ (by omega)
  obtain ⟨a,b,ma,mb,na,nb,inter,fa,fb⟩ := interlacing_of_cuts _ _ hp hq val inc endp
    (fun i => eval_opposite (pos _ (by omega)) (pos _ (by omega)) (oldSigns i))
    (fun i => eval_opposite (pos _ (by omega)) (pos _ (by omega)) (newSigns i))
  refine ⟨a,b,ma,mb,na,nb,inter,?_,?_⟩
  · rw [revstackDescentPolynomial_eq _ hn,←P,fa]
  · rw [revstackDescentPolynomial_eq _ (by omega),←Q,fb]

end DukesRevstack
