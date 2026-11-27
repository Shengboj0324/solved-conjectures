import Conjectures.ErdosGyarfasSpectrumTotals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort

/-! Select one point of each degree in increasing order. The lowest and
highest halves are disjoint, and their degree sums have explicit upper bounds. -/

namespace ErdosGyarfasSpectrum

variable {V : Type*} [DecidableEq V] {P : Finset V} {lines : Finset (Finset V)}

def degrees (P : Finset V) (lines : Finset (Finset V)) := P.image (degree lines)

theorem degrees_lt_order (space : LinearOn P lines) : (degrees P lines).card<P.card := by
  have inc : degrees P lines ⊆ (Finset.range P.card).erase 0 := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_erase.mpr ⟨Nat.ne_of_gt (degree_pos space hp),Finset.mem_range.mpr (degree_lt space hp)⟩
  have count := Finset.card_le_card inc
  have n := space.order
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)),Finset.card_range] at count
  omega

private theorem ordered_gap {f : ℕ} (u : Fin f → ℕ) (h : StrictMono u) (i j : Fin f) (hij : i≤j) :
    u i+(j.val-i.val) ≤ u j := by
  have add (d : ℕ) (hd : i.val+d<f) : u i+d ≤ u ⟨i.val+d,hd⟩ := by
    induction d with
    | zero => simp
    | succ d ih =>
      have prev := ih (by omega)
      have step := h (show (⟨i.val+d,by omega⟩ : Fin f)<⟨i.val+(d+1),hd⟩ by
        change i.val+d < i.val+(d+1); omega)
      omega
  have v : i.val+(j.val-i.val)=j.val := by have h' : i.val≤j.val := hij; omega
  have hg := add (j.val-i.val) (by rw [v]; exact j.isLt)
  have he : (⟨i.val+(j.val-i.val),by rw [v]; exact j.isLt⟩ : Fin f)=j := Fin.ext v
  rwa [he] at hg

private theorem sum_positions (t : ℕ) : 2*(∑ i : Fin t,(i.val : ℤ))=(t : ℤ)*(t-1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_succ]
    linarith

theorem representative_sets (space : LinearOn P lines) {f t : ℕ}
    (hf : (degrees P lines).card=f) (ht : t=f/2) (pos : 0<f) :
    ∃ X Y : Finset V, X⊆P ∧ Y⊆P ∧ Disjoint X Y ∧ X.card=t ∧ Y.card=t ∧
      2*lowTotal lines X ≤ (t : ℤ)*(t+1)+2*t*((P.card : ℤ)-f-1) ∧
      lowTotal lines X+highTotal P lines Y-(t : ℤ)^2 ≤ (t : ℤ)*((P.card : ℤ)-f-1) := by
  classical
  let u := (degrees P lines).orderEmbOfFin hf
  have avail (i : Fin f) : ∃ p∈P,degree lines p=u i :=
    Finset.mem_image.mp ((degrees P lines).orderEmbOfFin_mem hf i)
  choose rep hr hrep using avail
  have inj : Function.Injective rep := by
    intro i j eq
    exact u.injective ((hrep i).symm.trans ((congrArg (degree lines) eq).trans (hrep j)))
  let lo (i : Fin t) : Fin f := ⟨i.val,by have := i.isLt; omega⟩
  let hi (i : Fin t) : Fin f := ⟨f-1-i.val,by omega⟩
  let last : Fin f := ⟨f-1,by omega⟩
  have low_inj : Function.Injective fun i => rep (lo i) := by
    intro i j h
    have eq := congrArg (fun x : Fin f => x.val) (inj h)
    exact Fin.ext eq
  have high_inj : Function.Injective fun i => rep (hi i) := by
    intro i j h
    have eq := congrArg Fin.val (inj h)
    dsimp [hi] at eq
    apply Fin.ext; have := i.isLt; have := j.isLt; omega
  let X := Finset.univ.image (fun i : Fin t => rep (lo i))
  let Y := Finset.univ.image (fun i : Fin t => rep (hi i))
  have hx : X.card=t := by simp [X,Finset.card_image_of_injective _ low_inj]
  have hy : Y.card=t := by simp [Y,Finset.card_image_of_injective _ high_inj]
  have subset {g : Fin t → Fin f} : Finset.univ.image (fun i => rep (g i)) ⊆ P := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact hr _
  have disj : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro p px py
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp px
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp py
    have v := congrArg Fin.val (inj eq)
    dsimp [lo,hi] at v
    have := i.isLt; have := j.isLt; omega
  have low_sum : lowTotal lines X=∑ i : Fin t,(u (lo i) : ℤ) := by
    unfold lowTotal X
    rw [Finset.sum_image (fun i _ j _ e => low_inj e)]
    simp only [hrep]
  have high_sum : highTotal P lines Y=∑ i : Fin t,((P.card : ℤ)-1-u (hi i)) := by
    unfold highTotal Y
    rw [Finset.sum_image (fun i _ j _ e => high_inj e)]
    simp only [hrep]
  have largest : u last<P.card := (hrep last) ▸ degree_lt space (hr last)
  have low_bound (i : Fin t) : (u (lo i) : ℤ) ≤ (P.card : ℤ)-f+i.val := by
    have g := ordered_gap u u.strictMono (lo i) last (show (lo i).val≤last.val by
      dsimp [lo,last]; have := i.isLt; omega)
    change u (lo i)+(f-1-i.val) ≤ u last at g
    have := i.isLt; omega
  have pair_bound (i : Fin t) : (u (lo i) : ℤ)+((P.card : ℤ)-1-u (hi i)) ≤ (P.card : ℤ)-f+2*i.val := by
    have g := ordered_gap u u.strictMono (lo i) (hi i) (show (lo i).val≤(hi i).val by
      dsimp [lo,hi]; have := i.isLt; omega)
    change u (lo i)+(f-1-i.val-i.val) ≤ u (hi i) at g
    have := i.isLt; omega
  have l := Finset.sum_le_sum (s := Finset.univ) (fun i _ => low_bound i)
  have p := Finset.sum_le_sum (s := Finset.univ) (fun i _ => pair_bound i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,←Finset.mul_sum] at l p
  refine ⟨X,Y,subset,subset,disj,hx,hy,?_,?_⟩
  · rw [low_sum]; nlinarith [sum_positions t]
  · rw [low_sum,high_sum]; nlinarith [sum_positions t]

end ErdosGyarfasSpectrum
