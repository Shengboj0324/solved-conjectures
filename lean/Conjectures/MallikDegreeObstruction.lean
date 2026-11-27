import Conjectures.MallikDegreeGraphs

/-! A prescribed matching cannot be completed when some unused left
vertices have too few available right neighbors. -/

namespace MallikDegree

variable {α : Type*}

theorem obstruction {R : α → α → Prop} {k : ℕ} (u v : Fin k ↪ α) (edge : ∀ i,R (u i) (v i))
    (X Y : Finset α) (unused : ∀ x∈X,∀ i,x≠u i)
    (cover : ∀ x∈X,∀ y,R x y → (∀ i,y≠v i) → y∈Y) (small : Y.card<X.card) :
    ¬Extends R k := by
  classical
  intro canExtend
  obtain ⟨f,all,fixed⟩ := canExtend u v edge
  have sub : X.map f.toEmbedding⊆Y := by
    intro b hb
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hb
    apply cover x hx (f x) (all x)
    intro i eq
    exact unused x hx i (f.injective (eq.trans (fixed i).symm))
  have size := Finset.card_le_card sub
  rw [Finset.card_map] at size
  omega

theorem isolated_after_matching {R : α → α → Prop} {k : ℕ} (u v : Fin k ↪ α) (edge : ∀ i,R (u i) (v i))
    (x : α) (unused : ∀ i,x≠u i) (saturated : ∀ y,R x y → ∃ i,y=v i) : ¬Extends R k := by
  apply obstruction u v edge {x} ∅
  · intro a ha
    simpa only [Finset.mem_singleton.mp ha] using unused
  · intro a ha y hy fresh
    rw [Finset.mem_singleton.mp ha] at hy
    obtain ⟨i,eq⟩ := saturated y hy
    exact (fresh i eq).elim
  · simp

theorem extends_transpose {R : α → α → Prop} {k : ℕ} (extend : Extends R k) :
    Extends (fun x y => R y x) k := by
  intro u v edge
  obtain ⟨f,all,fixed⟩ := extend v u edge
  refine ⟨f.symm,?_,?_⟩
  · intro x
    simpa only [Equiv.apply_symm_apply] using all (f.symm x)
  · intro i
    exact f.symm_apply_eq.mpr (fixed i).symm

end MallikDegree
