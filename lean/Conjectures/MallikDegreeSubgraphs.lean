import Conjectures.MallikDegreeEdgeMatchings
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card

/-! Translate finite sets of disjoint bipartite edges to and from actual
Mathlib matching subgraphs, preserving their unordered edge counts. -/

namespace MallikDegree

variable {α : Type*} {R : α → α → Prop}

def subOfEdges (E : Finset (α × α)) (allowed : ∀ e∈E,R e.1 e.2) : (graph R).Subgraph where
  verts := {v | match v with
    | .inl x => ∃ y,(x,y)∈E
    | .inr y => ∃ x,(x,y)∈E}
  Adj := across (fun x y => (x,y)∈E)
  adj_sub := by
    intro v w edge
    cases v with
    | inl x => cases w with
      | inl a => exact False.elim edge
      | inr b => exact allowed (x,b) edge
    | inr y => cases w with
      | inl a => exact allowed (a,y) edge
      | inr b => exact False.elim edge
  edge_vert := by
    intro v w edge
    cases v with
    | inl x => cases w with
      | inl a => exact False.elim edge
      | inr b => exact ⟨b,edge⟩
    | inr y => cases w with
      | inl a => exact ⟨a,edge⟩
      | inr b => exact False.elim edge
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩

theorem subOfEdges_matching (E : Finset (α × α)) (m : EdgeMatching R E) : (subOfEdges E m.1).IsMatching := by
  intro v hv
  cases v with
  | inl x =>
    obtain ⟨y,hy⟩ := hv
    refine ⟨.inr y,hy,?_⟩
    rintro (b|b) hb
    · exact False.elim hb
    · exact congrArg Sum.inr (congrArg Prod.snd (m.2.1 hb hy rfl))
  | inr y =>
    obtain ⟨x,hx⟩ := hv
    refine ⟨.inl x,hx,?_⟩
    rintro (a|a) ha
    · exact congrArg Sum.inl (congrArg Prod.fst (m.2.2 ha hx rfl))
    · exact False.elim ha

variable [Fintype α]

noncomputable def edgePairs (M : (graph R).Subgraph) : Finset (α × α) := by
  classical exact Finset.univ.filter fun e => M.Adj (.inl e.1) (.inr e.2)

theorem mem_edgePairs (M : (graph R).Subgraph) (x y : α) :
    (x,y)∈edgePairs M ↔ M.Adj (.inl x) (.inr y) := by classical simp [edgePairs]

theorem pairs_of_edges (E : Finset (α × α)) (allowed : ∀ e∈E,R e.1 e.2) :
    edgePairs (subOfEdges E allowed)=E := by
  ext ⟨x,y⟩
  exact mem_edgePairs _ x y

theorem edgePairs_matching {M : (graph R).Subgraph} (m : M.IsMatching) : EdgeMatching R (edgePairs M) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨x,y⟩ e
    exact M.adj_sub ((mem_edgePairs ..).mp e)
  · rintro ⟨x,y⟩ e ⟨a,b⟩ h eq
    change x=a at eq
    subst a
    exact Prod.ext rfl (Sum.inr.inj (m.eq_of_adj_left ((mem_edgePairs ..).mp e) ((mem_edgePairs ..).mp h)))
  · rintro ⟨x,y⟩ e ⟨a,b⟩ h eq
    change y=b at eq
    subst b
    exact Prod.ext (Sum.inl.inj (m.eq_of_adj_right ((mem_edgePairs ..).mp e) ((mem_edgePairs ..).mp h))) rfl

omit [Fintype α] in
private theorem edgeName_injective : Function.Injective (fun e : α × α => s(Sum.inl e.1,Sum.inr e.2)) := by
  rintro ⟨x,y⟩ ⟨a,b⟩ eq
  rcases Sym2.eq_iff.mp eq with ⟨h,j⟩|⟨h,_⟩
  · exact Prod.ext (Sum.inl.inj h) (Sum.inr.inj j)
  · cases h

theorem edgePairs_card (M : (graph R).Subgraph) : (edgePairs M).card=M.edgeSet.ncard := by
  let name (e : α × α) := s(Sum.inl e.1,Sum.inr e.2)
  have eq : M.edgeSet=name '' (edgePairs M : Set (α × α)) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.Subgraph.mem_edgeSet]
      constructor
      · intro adj
        cases a with
        | inl x => cases b with
          | inl y => exact False.elim (M.adj_sub adj)
          | inr y => exact ⟨(x,y),(mem_edgePairs ..).mpr adj,rfl⟩
        | inr y => cases b with
          | inl x => exact ⟨(x,y),(mem_edgePairs ..).mpr adj.symm,Sym2.eq_swap⟩
          | inr x => exact False.elim (M.adj_sub adj)
      · rintro ⟨⟨x,y⟩,mem,eq⟩
        have edge := (mem_edgePairs M x y).mp mem
        rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact edge
        · exact edge.symm
  rw [eq,Set.ncard_image_of_injective _ edgeName_injective,Set.ncard_coe_finset]

end MallikDegree
