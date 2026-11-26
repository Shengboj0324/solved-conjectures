import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

/-! Normal-play dominating-set games. The position is the shared set picked
so far. Every unchosen vertex is legal until that set dominates the graph. -/

namespace FiscusGrid

variable {V : Type*} [Fintype V] [DecidableEq V]

def Dominates (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v, ∃ u ∈ S, u=v ∨ G.Adj u v

def winsWithin (G : SimpleGraph V) : ℕ → Finset V → Prop
  | 0, _ => False
  | n+1, S => ¬Dominates G S ∧ ∃ v, v∉S ∧ ¬winsWithin G n (insert v S)

def Wins (G : SimpleGraph V) (S : Finset V) : Prop :=
  winsWithin G (Fintype.card V-S.card) S

theorem wins_iff (G : SimpleGraph V) (S : Finset V) :
    Wins G S ↔ ¬Dominates G S ∧ ∃ v, v∉S ∧ ¬Wins G (insert v S) := by
  by_cases exhausted : S=Finset.univ
  · subst S
    have dom : Dominates G Finset.univ := fun v => ⟨v,Finset.mem_univ _,Or.inl rfl⟩
    simp [Wins,winsWithin,dom]
  · have smaller : S.card<Fintype.card V := (Finset.card_lt_iff_ne_univ S).mpr exhausted
    have eq : Fintype.card V-S.card=(Fintype.card V-S.card-1)+1 := by omega
    unfold Wins
    rw [eq,winsWithin]
    apply and_congr_right
    intro _
    apply exists_congr
    intro v
    apply and_congr_right
    intro hv
    rw [Finset.card_insert_of_notMem hv]
    have : Fintype.card V-(S.card+1)=Fintype.card V-S.card-1 := by omega
    rw [this]

abbrev Vertex := Fin 2 × Fin 7

def grid (a b : ℕ) := (SimpleGraph.pathGraph a).boxProd (SimpleGraph.pathGraph b)

def number (p : Vertex) : Fin 14 := ⟨7*p.1.val+p.2.val,by have := p.1.isLt; have := p.2.isLt; omega⟩

def vertex (i : Fin 14) : Vertex :=
  (⟨i.val/7,by have := i.isLt; omega⟩,⟨i.val%7,Nat.mod_lt _ (by decide)⟩)

@[simp] theorem number_vertex (i : Fin 14) : number (vertex i)=i := by
  apply Fin.ext
  simp only [number,vertex]
  omega

@[simp] theorem vertex_number (p : Vertex) : vertex (number p)=p := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [number,vertex] <;> have := p.2.isLt <;> omega

def picked (s : ℕ) : Finset Vertex :=
  Finset.univ.filter fun p => s.testBit (number p).val

@[simp] theorem mem_picked (s : ℕ) (p : Vertex) : p∈picked s ↔ s.testBit (number p).val = true := by
  simp [picked]

theorem picked_insert (s : ℕ) (i : Fin 14) :
    picked (s ||| 2^i.val) = insert (vertex i) (picked s) := by
  ext p
  simp only [mem_picked,Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq,
    Finset.mem_insert]
  have h : i.val=(number p).val ↔ p=vertex i := by
    constructor
    · intro h; rw [Fin.ext h,vertex_number]
    · rintro rfl; simp
  tauto

end FiscusGrid
