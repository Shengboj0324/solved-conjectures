import Conjectures.MonophonicPrismConstruction
import Conjectures.MonophonicPrismData

/-! Relabeling the triangular prism in the port coordinates used by the
all-order construction gives exactly the independently tabulated graph. -/

namespace MonophonicProduct

def stationIndex (u : Station 3) : Fin 6 := ⟨3*u.1.val+u.2.val,by have := u.1.isLt; have := u.2.isLt; omega⟩

def portIndex (v : Port 3) : Fin 18 :=
  ⟨3*(stationIndex v.1).val+v.2.val,by have := (stationIndex v.1).isLt; have := v.2.isLt; omega⟩

def prismEncoding : PrismVertex 3 → Vertex
  | .inl p => (#[0, 1, 2, 4, 3, 5, 6, 7, 8, 10, 11, 9, 14, 13, 12, 16, 17, 15] : Array Vertex)[(portIndex p).val]'((portIndex p).isLt)
  | .inr (.inl p) => (#[18, 21, 19, 24, 25, 26, 29, 31, 30, 35, 34, 33, 40, 38, 39, 44, 43, 42] : Array Vertex)[(portIndex p).val]'((portIndex p).isLt)
  | .inr (.inr (.inl u)) => (#[20, 27, 22, 36, 41, 37] : Array Vertex)[(stationIndex u).val]'((stationIndex u).isLt)
  | .inr (.inr (.inr i)) => (#[23, 28, 32] : Array Vertex)[i.val]'(i.isLt)

theorem encoding_surjective : ∀ b,∃ a,prismEncoding a=b := by decide +kernel
theorem encoding_injective : Function.Injective prismEncoding :=
  ((Fintype.bijective_iff_surjective_and_card prismEncoding).2
    ⟨encoding_surjective,by rw [vertex_count];rfl⟩).1
theorem encoding_adjacency : ∀ a b,witnessGraph.Adj (prismEncoding a) (prismEncoding b) ↔ (subdivision 3).Adj a b :=
  by decide +kernel

noncomputable def prismIso : subdivision 3 ≃g witnessGraph where
  toEquiv := Equiv.ofBijective prismEncoding ⟨encoding_injective,encoding_surjective⟩
  map_rel_iff' := encoding_adjacency _ _

theorem valid_pullback {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {k : ℕ} {col : W → Fin k} (valid : ValidColoring H col) :
    ValidColoring G (fun v => col (e v)) := by
  constructor
  · intro a b adj
    exact valid.proper _ _ (e.map_rel_iff.2 adj)
  · intro n p hp i j l ij il jl eqj
    have h : InducedPath H (fun v => e (p v)) :=
      ⟨fun a b eq => hp.1 a b (e.injective eq),fun a b => e.map_rel_iff.trans (hp.2 a b)⟩
    exact valid.monophonic _ h i j l ij il jl eqj

theorem number_pullback {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {k : ℕ} (h : ChromaticNumber H k) : ChromaticNumber G k := by
  obtain ⟨⟨c,vc⟩,lower⟩:=h
  exact ⟨⟨_,valid_pullback e vc⟩,fun m ⟨_,v⟩ => lower m ⟨_,valid_pullback e.symm v⟩⟩

end MonophonicProduct
