import Conjectures.MallikDegreeGraphs

/-! Relabel either side of a balanced graph without changing matching
extension or minimality. -/

namespace MallikDegree

variable {α β : Type*} {R : α → α → Prop} {Q : β → β → Prop}

def graphIso (a b : α ≃ β) (same : ∀ x y,R x y ↔ Q (a x) (b y)) : graph R ≃g graph Q where
  toEquiv := a.sumCongr b
  map_rel_iff' := by
    rintro (x|y) (z|w)
    · rfl
    · exact (same x w).symm
    · exact (same z y).symm
    · rfl

theorem relabel_extends (a b : α ≃ β) (same : ∀ x y,R x y ↔ Q (a x) (b y)) {k : ℕ}
    (extend : Extends R k) : Extends Q k := by
  intro u v edge
  let u' := u.trans a.symm.toEmbedding
  let v' := v.trans b.symm.toEmbedding
  have input (i : Fin k) : R (u' i) (v' i) := (same _ _).mpr (by simpa [u',v'] using edge i)
  obtain ⟨f,perfect,cover⟩ := extend u' v' input
  let g := (a.symm.trans f).trans b
  refine ⟨g,?_,?_⟩
  · intro x
    simpa [g] using (same _ _).mp (perfect (a.symm x))
  · intro i
    have eq := congrArg b (cover i)
    simpa [g,u',v'] using eq

variable [Fintype α] [Fintype β]

theorem relabel_extendable (a b : α ≃ β) (same : ∀ x y,R x y ↔ Q (a x) (b y)) {k : ℕ}
    (extend : Extendable R k) : Extendable Q k := by
  obtain ⟨conn,order,⟨u,v,edge⟩,can⟩ := extend
  refine ⟨(graphIso a b same).connected_iff.mp conn,?_,?_,relabel_extends a b same can⟩
  · rwa [←Fintype.card_congr a]
  · exact ⟨u.trans a.toEmbedding,v.trans b.toEmbedding,fun i => (same _ _).mp (edge i)⟩

theorem relabel_minimal (a b : α ≃ β) (same : ∀ x y,R x y ↔ Q (a x) (b y)) {k : ℕ} (minim : Minimal R k) :
    Minimal Q k := by
  refine ⟨relabel_extendable a b same minim.1,?_⟩
  intro p q edge can
  have rev (x y : β) : Q x y ↔ R (a.symm x) (b.symm y) := by simpa using (same (a.symm x) (b.symm y)).symm
  have cut (x y : β) : deleted Q p q x y ↔ deleted R (a.symm p) (b.symm q) (a.symm x) (b.symm y) := by
    exact and_congr (rev x y) (or_congr (not_congr a.symm.injective.eq_iff.symm)
      (not_congr b.symm.injective.eq_iff.symm))
  exact minim.2 _ _ ((rev p q).mp edge) (relabel_extendable a.symm b.symm cut can)

end MallikDegree
