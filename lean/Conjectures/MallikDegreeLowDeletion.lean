import Conjectures.MallikDegreeFamily
import Conjectures.MallikDegreeObstruction

/-! After deleting a low--low or a low--high edge, a literal matching
saturates every remaining neighbor of an uncovered low vertex. -/

namespace MallikDegree

variable {k t : ℕ}

theorem avoid_low (l : Fin t) (h : k<t) : ∃ g : Fin k ↪ Fin t,∀ i,g i≠l := by
  let T := (Finset.univ : Finset (Fin t)).erase l
  have card : Fintype.card (Fin k)≤Fintype.card T := by simp [T]; omega
  obtain ⟨u⟩ := Function.Embedding.nonempty_of_card_le card
  exact ⟨u.trans (Function.Embedding.subtype _),fun i => (Finset.mem_erase.mp (u i).property).1⟩

theorem delete_low_diagonal (D : Finset (Fin k)) (l : Fin t) (gap : k<t) :
    ¬Extends (deleted (family D) (.inr l) (.inr l)) k := by
  obtain ⟨g,skip⟩ := avoid_low l gap
  let u : Fin k ↪ Fin k ⊕ Fin t := g.trans Function.Embedding.inr
  let v : Fin k ↪ Fin k ⊕ Fin t := Function.Embedding.inl
  apply isolated_after_matching u v (x := Sum.inr l)
  · intro i
    exact ⟨trivial,Or.inr (by simp [v])⟩
  · intro i eq
    exact skip i (Sum.inr.inj eq).symm
  · intro y hy
    cases y with
    | inl i => exact ⟨i,rfl⟩
    | inr b =>
      obtain ⟨pair,missing⟩ := hy
      change l=b at pair
      subst b
      exact (missing.elim (fun h => h rfl) (fun h => h rfl)).elim

def lowSwitch (g : Fin k ↪ Fin t) (h : Fin k) : Fin k ↪ Fin k ⊕ Fin t where
  toFun i := if i=h then .inl h else .inr (g i)
  inj' := by
    intro i j eq
    by_cases ih : i=h <;> by_cases jh : j=h <;> simp_all

def highSwitch (l : Fin t) (h : Fin k) : Fin k ↪ Fin k ⊕ Fin t where
  toFun i := if i=h then .inr l else .inl i
  inj' := by
    intro i j eq
    by_cases ih : i=h <;> by_cases jh : j=h <;> simp_all

@[simp] theorem lowSwitch_apply (g : Fin k ↪ Fin t) (h i : Fin k) :
    lowSwitch g h i=(if i=h then .inl h else .inr (g i)) := rfl

@[simp] theorem highSwitch_apply (l : Fin t) (h i : Fin k) :
    highSwitch l h i=(if i=h then .inr l else .inl i) := rfl

theorem delete_low_high (D : Finset (Fin k)) (l : Fin t) (h : Fin k) (gap : k<t) :
    ¬Extends (deleted (family D) (.inr l) (.inl h)) k := by
  obtain ⟨g,skip⟩ := avoid_low l gap
  apply isolated_after_matching (lowSwitch g h) (highSwitch l h) (x := Sum.inr l)
  · intro i
    by_cases eq : i=h
    · simp [deleted,family,eq]
    · simp [deleted,family,eq]
  · intro i
    by_cases eq : i=h <;> simp [eq,Ne.symm (skip i)]
  · intro y edge
    cases y with
    | inl j =>
      have ne : j≠h := by
        intro eq
        subst j
        exact edge.2.elim (fun h => h rfl) (fun h => h rfl)
      exact ⟨j,by simp [ne]⟩
    | inr b =>
      have eq : l=b := edge.1
      exact ⟨h,by simp [eq]⟩

theorem delete_high_low (D : Finset (Fin k)) (h : Fin k) (l : Fin t) (gap : k<t) :
    ¬Extends (deleted (family D) (.inl h) (.inr l)) k := by
  intro extend
  have mirror := extends_transpose extend
  have eq : (fun (x y : Fin k ⊕ Fin t) => deleted (family D) (.inl h) (.inr l) y x)=
      deleted (family D) (.inr l) (.inl h) := by
    funext x y
    exact propext (and_congr (family_symm D y x) or_comm)
  rw [eq] at mirror
  exact delete_low_high D l h gap mirror

end MallikDegree
