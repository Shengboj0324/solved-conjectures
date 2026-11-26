import Conjectures.MallikDegreeFamily
import Conjectures.MallikDegreeObstruction
import Mathlib.Data.Fin.Embedding

/-! Deleting a high diagonal edge leaves too few neighbors for the k
high vertices after prescribing k low diagonal edges. -/

namespace MallikDegree

theorem delete_high_diagonal {k t : ℕ} (D : Finset (Fin k)) (h : Fin k) (hd : h∈D)
    (kt : k≤t) (balance : D.card+t=2*k) :
    ¬Extends (deleted (family (L := Fin t) D) (.inl h) (.inl h)) k := by
  let g := Fin.castLEEmb kt
  let u : Fin k ↪ Fin k ⊕ Fin t := g.trans Function.Embedding.inr
  let X : Finset (Fin k ⊕ Fin t) := Finset.univ.map Function.Embedding.inl
  let Y : Finset (Fin k ⊕ Fin t) := (D.erase h).disjSum (Finset.univ \ occupied g)
  apply obstruction u u (X := X) (Y := Y)
  · intro i
    exact ⟨rfl,Or.inl (by simp [u])⟩
  · intro x hx i
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hx
    simp [u]
  · intro x hx y edge fresh
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hx
    cases y with
    | inl z =>
      obtain ⟨pair,keep⟩ := edge
      obtain ⟨eq,mem⟩ := pair
      subst z
      have ne : j≠h := by
        intro bad
        subst j
        exact keep.elim (fun p => p rfl) (fun p => p rfl)
      exact Finset.inl_mem_disjSum.mpr (Finset.mem_erase.mpr ⟨ne,mem⟩)
    | inr z =>
      apply Finset.inr_mem_disjSum.mpr
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro used
      obtain ⟨i,_,eq⟩ := Finset.mem_map.mp used
      exact fresh i (congrArg Sum.inr eq.symm)
  · have whole := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (occupied g))
    rw [occupied_card,Finset.card_univ,Fintype.card_fin] at whole
    have pos := Finset.card_pos.mpr ⟨h,hd⟩
    change ((D.erase h).disjSum (Finset.univ \ occupied g)).card<(Finset.univ.map
      (Function.Embedding.inl : Fin k ↪ Fin k ⊕ Fin t)).card
    rw [Finset.card_disjSum,Finset.card_erase_of_mem hd,Finset.card_map,Finset.card_univ,Fintype.card_fin]
    omega

end MallikDegree
