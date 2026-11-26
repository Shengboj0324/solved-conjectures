import Conjectures.MonophonicProductPaths
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fintype.EquivFin

/-! Triangle-expanded prisms and their single-edge subdivisions. A station
is a vertex of one of the two original rings. Its three ports point forward,
backward and along the rung, in that order. -/

namespace MonophonicProduct

abbrev Station (s : ℕ) := Fin 2 × Fin s
abbrev Port (s : ℕ) := Station s × Fin 3
abbrev PrismEdge (s : ℕ) := Port s ⊕ (Station s ⊕ Fin s)
abbrev PrismVertex (s : ℕ) := Port s ⊕ PrismEdge s

def prismEnds (s : ℕ) : PrismEdge s → Port s × Port s
  | .inl (u,j) => ((u,j),(u,finRotate 3 j))
  | .inr (.inl (r,i)) => (((r,i),0),((r,finRotate s i),1))
  | .inr (.inr i) => (((0,i),2),((1,i),2))

def incident (s : ℕ) (v : Port s) (e : PrismEdge s) := v=(prismEnds s e).1 ∨ v=(prismEnds s e).2

def prismAdj (s : ℕ) : PrismVertex s → PrismVertex s → Prop
  | .inl p,.inr e => incident s p e
  | .inr e,.inl p => incident s p e
  | _,_ => False

def subdivision (s : ℕ) : SimpleGraph (PrismVertex s) where
  Adj := prismAdj s
  symm := ⟨fun a b h => by cases a <;> cases b <;> exact h⟩
  loopless := ⟨fun a => by cases a <;> exact id⟩

instance (s : ℕ) : DecidableRel (subdivision s).Adj := by
  intro a b
  cases a <;> cases b <;> unfold subdivision prismAdj <;> dsimp only
  all_goals first | exact isFalse id | unfold incident; infer_instance

theorem edge_count (s : ℕ) : Fintype.card (PrismEdge s)=9*s := by
  simp only [PrismEdge,Port,Station,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin]
  omega

theorem vertex_count (s : ℕ) : Fintype.card (PrismVertex s)=15*s := by
  simp only [PrismVertex,Fintype.card_sum,Port,Station,Fintype.card_prod,Fintype.card_fin]
  omega

def dualLabel (s : ℕ) : PrismVertex s → PrismEdge s
  | .inl p => .inl p
  | .inr e => e

theorem dual_label_pair (s : ℕ) (a b : PrismVertex s) (same : dualLabel s a=dualLabel s b) :
    a=b ∨ (subdivision s).Adj a b := by
  cases a with
  | inl p =>
    cases b with
    | inl q => exact Or.inl (congrArg Sum.inl (Sum.inl.inj same))
    | inr e =>
      change Sum.inl p=e at same
      subst e
      exact Or.inr (Or.inl rfl)
  | inr e =>
    cases b with
    | inl q =>
      change e=Sum.inl q at same
      subst e
      exact Or.inr (Or.inl rfl)
    | inr e' => exact Or.inl (congrArg Sum.inr same)

theorem dual_label_at_most_two (s : ℕ) (a b c : PrismVertex s)
    (ab : dualLabel s a=dualLabel s b) (ac : dualLabel s a=dualLabel s c) :
    a=b ∨ a=c ∨ b=c := by
  cases a <;> cases b <;> cases c <;> simp_all [dualLabel]

theorem family_dual_exact (s : ℕ) : ChromaticNumber (subdivision s)ᶜ (9*s) := by
  classical
  let e : PrismEdge s ≃ Fin (9*s) := Fintype.equivFinOfCardEq (edge_count s)
  let col : PrismVertex s → Fin (9*s) := fun v => e (dualLabel s v)
  refine ⟨⟨col,?_⟩,?_⟩
  · constructor
    · intro a b adj same
      have dis := (SimpleGraph.compl_adj _ _ _).1 adj
      exact (dual_label_pair s a b (e.injective same)).elim dis.1 dis.2
    · intro n p hp i j l ij il jl eqj eql
      rcases dual_label_at_most_two s _ _ _ (e.injective eqj) (e.injective eql) with h | h | h
      · exact ij (hp.1 _ _ h)
      · exact il (hp.1 _ _ h)
      · exact jl (hp.1 _ _ h)
  · rintro k ⟨f,valid⟩
    let g (i : PrismEdge s) := f (Sum.inr i)
    have inj : Function.Injective g := by
      intro a b eq
      by_contra ne
      have adj : (subdivision s)ᶜ.Adj (Sum.inr a) (Sum.inr b) :=
        (SimpleGraph.compl_adj _ _ _).2 ⟨fun h => ne (Sum.inr.inj h),id⟩
      exact valid.proper _ _ adj eq
    simpa only [edge_count,Fintype.card_fin] using Fintype.card_le_of_injective g inj

end MonophonicProduct
