import Conjectures.MallikDegreeSubgraphs

/-! A perfect matching in the Mathlib graph is exactly a permutation of
the two parts that uses allowed edges. -/

namespace MallikDegree

variable {α : Type*} {R : α → α → Prop}

def perfectSubgraph (f : Equiv.Perm α) (edge : ∀ x,R x (f x)) : (graph R).Subgraph where
  verts := Set.univ
  Adj := across fun x y => f x=y
  edge_vert := by simp
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  adj_sub := by
    intro a b h
    cases a with
    | inl x => cases b with
      | inl y => exact False.elim h
      | inr y => exact (show f x=y from h) ▸ edge x
    | inr y => cases b with
      | inl x => exact (show f x=y from h) ▸ edge x
      | inr x => exact False.elim h

theorem perfectSubgraph_perfect (f : Equiv.Perm α) (edge : ∀ x,R x (f x)) :
    (perfectSubgraph f edge).IsPerfectMatching := by
  refine ⟨?_,fun _ => Set.mem_univ _⟩
  intro v _
  cases v with
  | inl x =>
    refine ⟨.inr (f x),rfl,?_⟩
    rintro (a|b) adj
    · exact False.elim adj
    · exact congrArg Sum.inr (Eq.symm (show f x=b from adj))
  | inr y =>
    refine ⟨.inl (f.symm y),f.apply_symm_apply y,?_⟩
    rintro (a|b) adj
    · exact congrArg Sum.inl (f.injective ((show f a=y from adj).trans (f.apply_symm_apply y).symm))
    · exact False.elim adj

theorem le_spanning_of_pairs {M P : (graph R).Subgraph} (span : P.IsSpanning)
    (sub : ∀ x y,M.Adj (.inl x) (.inr y) → P.Adj (.inl x) (.inr y)) : M≤P := by
  refine ⟨fun x _ => span x,?_⟩
  intro a b edge
  cases a with
  | inl x => cases b with
    | inl y => exact False.elim (M.adj_sub edge)
    | inr y => exact sub x y edge
  | inr y => cases b with
    | inl x => exact (sub x y edge.symm).symm
    | inr x => exact False.elim (M.adj_sub edge)

variable [Fintype α]

theorem permutation_of_perfect {P : (graph R).Subgraph} (perfect : P.IsPerfectMatching) :
    ∃ f : Equiv.Perm α,(∀ x,R x (f x)) ∧ ∀ x y,P.Adj (.inl x) (.inr y) ↔ f x=y := by
  classical
  have right (x : α) : ∃ y,P.Adj (.inl x) (.inr y) := by
    obtain ⟨a,adj,_⟩ := perfect.1 (perfect.2 (.inl x))
    cases a with
    | inl z => exact False.elim (P.adj_sub adj)
    | inr y => exact ⟨y,adj⟩
  choose f pair using right
  have inj : Function.Injective f := by
    intro x y eq
    have e := pair x
    rw [eq] at e
    exact Sum.inl.inj (perfect.1.eq_of_adj_right e (pair y))
  let perm := Equiv.ofBijective f ⟨inj,(Finite.injective_iff_surjective).mp inj⟩
  refine ⟨perm,fun x => P.adj_sub (pair x),?_⟩
  intro x y
  constructor
  · intro adj
    exact Sum.inr.inj (perfect.1.eq_of_adj_left (pair x) adj)
  · rintro rfl
    exact pair x

end MallikDegree
