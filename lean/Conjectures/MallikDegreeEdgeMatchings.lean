import Conjectures.MallikDegreeGraphs

/-! The tuple formulation ranges over exactly all k-edge matchings.
A perfect matching is the graph of a permutation between the two sides. -/

namespace MallikDegree

variable {α : Type*}

def EdgeMatching (R : α → α → Prop) (E : Finset (α × α)) : Prop :=
  (∀ e∈E,R e.1 e.2) ∧ Set.InjOn Prod.fst (E : Set (α × α)) ∧ Set.InjOn Prod.snd (E : Set (α × α))

def tupleEdges {k : ℕ} (u v : Fin k ↪ α) : Finset (α × α) :=
  Finset.univ.map ⟨fun i => (u i,v i),fun _ _ eq => u.injective (congrArg Prod.fst eq)⟩

theorem mem_tupleEdges {k : ℕ} (u v : Fin k ↪ α) (e : α × α) :
    e∈tupleEdges u v ↔ ∃ i,(u i,v i)=e := by
  simp only [tupleEdges,Finset.mem_map,Finset.mem_univ,true_and]
  rfl

theorem tupleEdges_card {k : ℕ} (u v : Fin k ↪ α) : (tupleEdges u v).card=k := by simp [tupleEdges]

theorem tupleEdges_matching {R : α → α → Prop} {k : ℕ} (u v : Fin k ↪ α) (edge : ∀ i,R (u i) (v i)) :
    EdgeMatching R (tupleEdges u v) := by
  refine ⟨?_,?_,?_⟩
  · intro e he
    obtain ⟨i,rfl⟩ := (mem_tupleEdges u v e).mp he
    exact edge i
  · intro e he b hb eq
    obtain ⟨i,rfl⟩ := (mem_tupleEdges u v e).mp he
    obtain ⟨j,rfl⟩ := (mem_tupleEdges u v b).mp hb
    rw [u.injective eq]
  · intro e he b hb eq
    obtain ⟨i,rfl⟩ := (mem_tupleEdges u v e).mp he
    obtain ⟨j,rfl⟩ := (mem_tupleEdges u v b).mp hb
    rw [v.injective eq]

theorem tupleEdges_surjective {R : α → α → Prop} (E : Finset (α × α)) {k : ℕ}
    (size : E.card=k) (mat : EdgeMatching R E) :
    ∃ u v : Fin k ↪ α,tupleEdges u v=E ∧ ∀ i,R (u i) (v i) := by
  let e := (Finset.equivFinOfCardEq size).symm
  let u : Fin k ↪ α := ⟨fun i => (e i).val.1,fun i j h =>
    e.injective (Subtype.ext (mat.2.1 (e i).property (e j).property h))⟩
  let v : Fin k ↪ α := ⟨fun i => (e i).val.2,fun i j h =>
    e.injective (Subtype.ext (mat.2.2 (e i).property (e j).property h))⟩
  refine ⟨u,v,?_,fun i => mat.1 (e i).val (e i).property⟩
  ext x
  rw [mem_tupleEdges]
  constructor
  · rintro ⟨i,rfl⟩
    exact (e i).property
  · intro hx
    obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
    exact ⟨i,congrArg Subtype.val hi⟩

theorem extends_iff_every_matching {R : α → α → Prop} {k : ℕ} : Extends R k ↔
    ∀ E : Finset (α × α),E.card=k → EdgeMatching R E →
      ∃ f : Equiv.Perm α,(∀ x,R x (f x)) ∧ ∀ e∈E,f e.1=e.2 := by
  constructor
  · intro extend E card mat
    obtain ⟨u,v,eq,edge⟩ := tupleEdges_surjective E card mat
    obtain ⟨f,perfect,cover⟩ := extend u v edge
    refine ⟨f,perfect,?_⟩
    intro e he
    rw [←eq] at he
    obtain ⟨i,rfl⟩ := (mem_tupleEdges u v e).mp he
    exact cover i
  · intro extend u v edge
    obtain ⟨f,perfect,cover⟩ := extend _ (tupleEdges_card u v) (tupleEdges_matching u v edge)
    exact ⟨f,perfect,fun i => cover (u i,v i) ((mem_tupleEdges ..).mpr ⟨i,rfl⟩)⟩

end MallikDegree
