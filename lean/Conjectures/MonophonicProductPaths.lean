import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-! Independent monophonic colorings use proper color classes meeting every
induced path in at most two vertices. An induced path is an injective vertex
sequence preserving and reflecting precisely the consecutive edges. -/

namespace MonophonicProduct

abbrev Vertex := Fin 45

def consecutive {n : ℕ} (i j : Fin n) : Prop := i.val+1=j.val ∨ j.val+1=i.val

def InducedPath {V : Type*} (G : SimpleGraph V) {n : ℕ} (p : Fin n → V) : Prop :=
  (∀ i j,p i=p j → i=j) ∧ ∀ i j,G.Adj (p i) (p j) ↔ consecutive i j

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (p : Fin n → V) : Decidable (InducedPath G p) := by
  unfold InducedPath consecutive
  infer_instance

def inducedEmbedding {V : Type*} {G : SimpleGraph V} {n : ℕ} {p : Fin n → V}
    (hp : InducedPath G p) : SimpleGraph.pathGraph n ↪g G where
  toFun := p
  inj' := fun _ _ h => hp.1 _ _ h
  map_rel_iff' := (hp.2 _ _).trans SimpleGraph.pathGraph_adj.symm

theorem embedding_induced {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (p : SimpleGraph.pathGraph n ↪g G) : InducedPath G p :=
  ⟨fun _ _ h => p.injective h,fun _ _ => p.map_rel_iff.trans SimpleGraph.pathGraph_adj⟩

structure ValidColoring {V : Type*} (G : SimpleGraph V) {k : ℕ} (col : V → Fin k) : Prop where
  proper : ∀ a b,G.Adj a b → col a≠col b
  monophonic : ∀ {n : ℕ} (p : Fin n → V),InducedPath G p → ∀ i j l,
    i≠j → i≠l → j≠l → col (p i)=col (p j) → col (p i)≠col (p l)

def HasColoring {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop := ∃ c : V → Fin k,ValidColoring G c

def ChromaticNumber {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  HasColoring G k ∧ ∀ m,HasColoring G m → k≤m

def sharedMask (a b : ℕ) : List ℕ → ℕ
  | [] => 0
  | m::ms => (if m.testBit a && m.testBit b then m else 0) ||| sharedMask a b ms

theorem sharedMask_mem (a b c : ℕ) (ms : List ℕ) :
    (sharedMask a b ms).testBit c=true ↔
      ∃ m∈ms,m.testBit a=true ∧ m.testBit b=true ∧ m.testBit c=true := by
  induction ms with
  | nil => simp [sharedMask]
  | cons m ms ih =>
    cases ha : m.testBit a <;> cases hb : m.testBit b <;>
      simp [sharedMask,ha,hb,ih]

end MonophonicProduct
