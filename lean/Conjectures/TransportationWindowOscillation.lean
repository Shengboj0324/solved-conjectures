import Conjectures.TransportationLogWindow
import Conjectures.TransportationLegendreOscillator
import Conjectures.TransportationRootDeficit

/-! Sturm intervals in Legendre coordinates yield distinct unperturbed
binomial roots in the logarithmic window. -/

namespace TransportationEhrhart

open Polynomial Set

noncomputable def windowFrequency (n : ℕ) := (n : ℝ)/(4*Real.sqrt (windowScale n))

theorem window_potential (n : ℕ) (hn : 0<(n : ℝ)) (hl : 32≤Real.log n) {x : ℝ}
    (hx : x∈Icc (legendreCoordinate (2*windowScale n)) (legendreCoordinate (windowScale n))) :
    0<legendreGap x ∧ windowFrequency n^2<legendrePotential n x := by
  obtain ⟨t0,th,_⟩ := window_scale n hn hl
  obtain ⟨x0,_,z⟩ := coordinate_window_inverse t0 (by linarith) hx
  have z0:=t0.trans_le z.1
  have bounds:=coordinate_gap_bounds z0.le (show legendreCoordinate x≤1 by linarith [z.2])
  rw [coordinate_involutive x0] at bounds
  have s0: 0<legendreGap x := z0.trans_le bounds.1
  have sup : legendreGap x≤8*windowScale n := by linarith [bounds.2,z.2]
  have eq : windowFrequency n^2=(n : ℝ)^2/(16*windowScale n) := by
    rw [windowFrequency,div_pow,mul_pow,Real.sq_sqrt t0.le]
    norm_num
  refine ⟨s0,?_⟩
  rw [eq,legendrePotential]
  apply lt_of_lt_of_le _ (le_add_of_nonneg_right (by positivity))
  apply (div_lt_div_iff₀ (by positivity) s0).2
  unfold legendreMass
  have up := mul_le_mul_of_nonneg_left sup (sq_nonneg (n : ℝ))
  have strict := mul_pos (sq_pos_of_pos hn) t0
  have extra := mul_pos hn t0
  nlinarith only [up,strict,extra]

theorem window_distinct_roots (n N : ℕ) (hn : 0<(n : ℝ)) (hl : 32≤Real.log n)
    (count : (N : ℝ)*4*Real.pi≤windowFrequency n*windowScale n) :
    N≤(rootsIn (binomialSquare n) (Icc (-(2*windowScale n)) (-windowScale n))).card := by
  classical
  obtain ⟨t0,th,_⟩ := window_scale n hn hl
  let t:=windowScale n
  let ω:=windowFrequency n
  let d:=Real.pi/ω
  let a:=legendreCoordinate (2*t)
  let b:=legendreCoordinate t
  have freq : 0<ω := div_pos hn (mul_pos (by norm_num) (Real.sqrt_pos.2 t0))
  have dpos : 0<d := div_pos Real.pi_pos freq
  have width : t/2≤b-a := coordinate_window_width t0.le (by dsimp [t]; linarith)
  have fit : 2*(N : ℝ)*d≤t/2 := by
    change 2*(N : ℝ)*(Real.pi/ω)≤t/2
    rw [←mul_div_assoc,div_le_iff₀ freq]
    dsimp [ω,t]
    nlinarith only [count]
  let lo (i : Fin N) := a+2*(i.val : ℝ)*d
  let hi (i : Fin N) := a+(2*(i.val : ℝ)+1)*d
  have sub (i : Fin N) : Icc (lo i) (hi i) ⊆ Icc a b := by
    have il : (i.val : ℝ)+1≤(N : ℝ) := by exact_mod_cast i.isLt
    apply Icc_subset_Icc
    · dsimp [lo]
      exact le_add_of_nonneg_right (by positivity)
    · dsimp [hi]
      have upper := mul_le_mul_of_nonneg_right il dpos.le
      nlinarith only [width,fit,upper,dpos]
  have each (i : Fin N) : ∃ x∈Icc (lo i) (hi i),(legendre n).eval x=0 := by
    apply legendre_interval_zero n (ω := ω)
    · dsimp [lo,hi]; linarith
    · exact freq
    · have period : ω*d=Real.pi := by dsimp [d]; field_simp
      dsimp [lo,hi]
      linear_combination period
    · exact fun x hx => (window_potential n hn hl (sub i hx)).1
    · exact fun x hx => (window_potential n hn hl (sub i ⟨hx.1.le,hx.2.le⟩)).2
  choose point inside root using each
  have strict : StrictMono point := by
    intro i j ij
    have sep : (i.val : ℝ)+1≤(j.val : ℝ) := by exact_mod_cast ij
    have scaled := mul_le_mul_of_nonneg_right sep dpos.le
    have l:=(inside i).2
    have r:=(inside j).1
    dsimp [lo,hi] at l r
    nlinarith only [l,r,scaled,dpos]
  have dom (i : Fin N) := coordinate_window_inverse t0 (by linarith) (sub i (inside i))
  let gr:=rootsIn (binomialSquare n) (Icc (-(2*t)) (-t))
  have mem (i : Fin N) : -legendreCoordinate (point i)∈gr := by
    have h:=(dom i).2.2
    apply mem_rootsIn.mpr
    refine ⟨(mem_roots (binomialSquare_ne_zero n)).2 ?_,neg_le_neg h.2,neg_le_neg h.1⟩
    change (binomialSquare n).eval (-legendreCoordinate (point i))=0
    rw [binomialSquare_transform n (t0.le.trans h.1),coordinate_involutive (dom i).1,root,mul_zero]
  let emb : Fin N → ↥gr.toFinset := fun i => ⟨_,Multiset.mem_toFinset.mpr (mem i)⟩
  have inj : Function.Injective emb := by
    intro i j h
    have eq : legendreCoordinate (point i)=legendreCoordinate (point j) := neg_injective (congrArg Subtype.val h)
    have forward := congrArg legendreCoordinate eq
    rw [coordinate_involutive (dom i).1,coordinate_involutive (dom j).1] at forward
    exact strict.injective forward
  exact (show N≤gr.toFinset.card by
    simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective emb inj).trans gr.toFinset_card_le

end TransportationEhrhart
