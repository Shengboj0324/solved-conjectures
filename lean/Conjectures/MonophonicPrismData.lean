import Conjectures.MonophonicProductPaths

/-! The 18 original cubic vertices are followed by 27 subdivision vertices.
The adjacency rows use bit number j for the edge to vertex j. The two
explicit colorings use the triangle ports of the expanded triangular prism. -/

namespace MonophonicProduct

def adjacencyRows : Array ℕ := #[1835008, 6553600, 11010048, 51380224, 218103808, 369098752, 1614807040, 2818572288, 7516192768, 25778192384, 111669149696, 188978561024, 824902156288, 1443109011456, 3848290697216, 13198434500608, 22127671508992, 28587302322176, 3, 5, 9, 6, 66, 516, 24, 40, 48, 144, 4128, 192, 320, 384, 33024, 1536, 2560, 3072, 9216, 67584, 12288, 20480, 24576, 147456, 98304, 163840, 196608]
def row (v : Vertex) : ℕ := adjacencyRows[v.val]'(by exact v.isLt)

theorem rows_symmetric : ∀ a b : Vertex,(row a).testBit b=(row b).testBit a := by decide +kernel
theorem rows_diagonal : ∀ a : Vertex,(row a).testBit a=false := by decide +kernel

def witnessGraph : SimpleGraph Vertex where
  Adj a b := (row a).testBit b=true
  symm := ⟨fun a b h => (rows_symmetric a b) ▸ h⟩
  loopless := ⟨fun a h => by change (row a).testBit a=true at h;rw [rows_diagonal] at h; contradiction⟩

instance : DecidableRel witnessGraph.Adj := fun a b => inferInstanceAs (Decidable ((row a).testBit b=true))

def original (c : Fin 18) : Vertex := ⟨c.val,by omega⟩
def star (c : Fin 18) : Finset Vertex := Finset.univ.filter fun v => (row (original c)).testBit v=true

theorem mem_star (c : Fin 18) (v : Vertex) : v∈star c ↔ witnessGraph.Adj (original c) v := by
  simp [star,witnessGraph]

def primalColors : Array (Fin 20) := #[6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 0, 0, 0, 15, 2, 15, 1, 16, 1, 1, 16, 2, 2, 17, 17, 3, 18, 3, 3, 5, 18, 4, 4, 4, 5, 19, 5]
def primal (v : Vertex) := primalColors[v.val]'(by exact v.isLt)
def dualColors : Array (Fin 27) := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0, 2, 18, 1, 19, 20, 3, 5, 4, 21, 22, 6, 8, 7, 23, 9, 11, 10, 24, 25, 12, 14, 13, 26, 15, 17, 16]
def dual (v : Vertex) := dualColors[v.val]'(by exact v.isLt)

def fiber {k : ℕ} (color : Vertex → Fin k) (c : Fin k) : Finset Vertex := Finset.univ.filter (color ·=c)

theorem mem_fiber {k : ℕ} (color : Vertex → Fin k) (c : Fin k) (v : Vertex) :
    v∈fiber color c ↔ color v=c := by simp [fiber]

end MonophonicProduct
