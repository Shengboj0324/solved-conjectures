import Conjectures.MonophonicPrismData

/-! Incidence, clique and explicit coloring facts for the 45-vertex graph. -/

namespace MonophonicProduct

theorem star_card : ∀ c : Fin 18,(star c).card=3 := by decide +kernel

theorem star_intersections : ∀ c d : Fin 18,c≠d → (star c ∩ star d).card≤1 := by decide +kernel

theorem triangle_overlap : ∀ c d : Fin 18,c.val/3=d.val/3 → ∃ v : Vertex,v∈star c ∧ v∈star d := by
  decide +kernel

def neighbors (v : Vertex) := Finset.univ.filter (witnessGraph.Adj v)

theorem mem_neighbors (v x : Vertex) : x∈neighbors v ↔ witnessGraph.Adj v x := by simp [neighbors]

theorem subdivision_degrees : ∀ c : Fin 18,∀ v∈star c,(neighbors v).card=2 := by decide +kernel

theorem subdivision_neighbors (c : Fin 18) (v : Vertex) (hv : v∈star c) (a b : Vertex)
    (ha : witnessGraph.Adj v a) (hb : witnessGraph.Adj v b) (ab : a≠b) : a=original c ∨ b=original c := by
  by_contra! h
  have hc := ((mem_star c v).1 hv).symm
  have three : 2<(neighbors v).card := Finset.two_lt_card_iff.mpr
    ⟨a,b,original c,(mem_neighbors ..).2 ha,(mem_neighbors ..).2 hb,(mem_neighbors ..).2 hc,ab,h.1,h.2⟩
  rw [subdivision_degrees c v hv] at three
  omega

theorem primal_proper : ∀ a b : Vertex,witnessGraph.Adj a b → primal a≠primal b := by decide +kernel

theorem primal_fibers : ∀ c : Fin 20,(fiber primal c).card≤2 ∨ ∃ s : Fin 18,fiber primal c⊆star s := by
  decide +kernel

theorem dual_proper : ∀ a b : Vertex,witnessGraphᶜ.Adj a b → dual a≠dual b := by decide +kernel

theorem dual_fibers : ∀ c : Fin 27,(fiber dual c).card≤2 := by decide +kernel

def subdivider (i : Fin 27) : Vertex := ⟨18+i.val,by omega⟩

theorem dual_clique : ∀ a b : Fin 27,a≠b → witnessGraphᶜ.Adj (subdivider a) (subdivider b) := by
  decide +kernel

theorem dual_lower {k : ℕ} {col : Vertex → Fin k} (h : ValidColoring witnessGraphᶜ col) : 27≤k := by
  let f (i : Fin 27) := col (subdivider i)
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    exact h.proper _ _ (dual_clique i j ne) eq
  simpa using Fintype.card_le_of_injective f inj

end MonophonicProduct
