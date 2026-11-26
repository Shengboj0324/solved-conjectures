import Conjectures.MallikDegreeFamily
import Conjectures.MallikDegreeHall
import Mathlib.Data.Fin.Embedding

/-! Verify connectivity, an actual matching of size k and the extension of
every matching of that size. -/

namespace MallikDegree

variable {H L : Type*} [DecidableEq H]

omit [DecidableEq H] in
theorem family_connected (D : Finset H) (h : H) (l : L) : (graph (family (L := L) D)).Connected := by
  let G := graph (family (L := L) D)
  let home : (H ⊕ L) ⊕ (H ⊕ L) := .inl (.inl h)
  have rightLow (j : L) : G.Reachable home (.inr (.inr j)) :=
    (show G.Adj home (.inr (.inr j)) from trivial).reachable
  have leftLow (j : L) : G.Reachable home (.inl (.inr j)) :=
    (rightLow j).trans (show G.Adj (.inr (.inr j)) (.inl (.inr j)) from rfl).reachable
  apply (G.connected_iff_exists_forall_reachable).mpr
  refine ⟨home,?_⟩
  rintro ((i|j)|(i|j))
  · exact (rightLow l).trans (show G.Adj (.inr (.inr l)) (.inl (.inl i)) from trivial).reachable
  · exact leftLow j
  · exact (leftLow l).trans (show G.Adj (.inl (.inr l)) (.inr (.inl i)) from trivial).reachable
  · exact rightLow j

theorem family_extendable {k t : ℕ} (D : Finset (Fin k)) (hk : 0<k) (ht : k≤t)
    (balance : D.card+t=2*k) : Extendable (family (L := Fin t) D) k := by
  let e : Fin k ↪ Fin k ⊕ Fin t := (Fin.castLEEmb ht).trans Function.Embedding.inr
  have conn := family_connected D (⟨0,hk⟩ : Fin k) (⟨0,by omega⟩ : Fin t)
  refine ⟨conn,by simp; omega,⟨e,e,fun _ => rfl⟩,extends_of_expansion ?_⟩
  intro X nonempty size
  simpa only [Fintype.card_fin] using family_expands D (by simpa only [Fintype.card_fin] using balance)
    X nonempty (by simpa only [Fintype.card_fin] using size)

end MallikDegree
