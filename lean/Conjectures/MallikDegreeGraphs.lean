import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! Literal balanced bipartite graphs, partial matchings and perfect
matchings as bijections between the two parts. -/

namespace MallikDegree

variable {α : Type*}

def across (R : α → α → Prop) : Sum α α → Sum α α → Prop
  | .inl x,.inr y => R x y
  | .inr y,.inl x => R x y
  | _,_ => False

def graph (R : α → α → Prop) : SimpleGraph (Sum α α) where
  Adj := across R
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> simp [across]⟩

def deleted (R : α → α → Prop) (x y : α) : α → α → Prop :=
  fun a b => R a b ∧ (a≠x ∨ b≠y)

def Extends (R : α → α → Prop) (k : ℕ) : Prop :=
  ∀ (u v : Fin k ↪ α), (∀ i,R (u i) (v i)) →
    ∃ f : Equiv.Perm α, (∀ x,R x (f x)) ∧ ∀ i,f (u i)=v i

def Extendable [Fintype α] (R : α → α → Prop) (k : ℕ) : Prop :=
  (graph R).Connected ∧ 2*k+2≤2*Fintype.card α ∧
    (∃ u v : Fin k ↪ α,∀ i,R (u i) (v i)) ∧ Extends R k

def Minimal [Fintype α] (R : α → α → Prop) (k : ℕ) : Prop :=
  Extendable R k ∧ ∀ x y, R x y → ¬Extendable (deleted R x y) k

noncomputable def neighbors [Fintype α] (R : α → α → Prop) (X : Finset α) : Finset α := by
  classical
  exact Finset.univ.filter fun y => ∃ x∈X,R x y

theorem mem_neighbors [Fintype α] {R : α → α → Prop} {X : Finset α} {y : α} :
    y∈neighbors R X ↔ ∃ x∈X,R x y := by classical simp [neighbors]

def Expands [Fintype α] (R : α → α → Prop) (k : ℕ) : Prop :=
  ∀ X : Finset α, X.Nonempty → X.card+k≤Fintype.card α → X.card+k≤(neighbors R X).card

def occupied {k : ℕ} (u : Fin k ↪ α) : Finset α := Finset.univ.map u

theorem mem_occupied {k : ℕ} (u : Fin k ↪ α) (i : Fin k) : u i∈occupied u :=
  Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem occupied_card {k : ℕ} (u : Fin k ↪ α) : (occupied u).card=k := by simp [occupied]

noncomputable def indexEquiv {k : ℕ} (u : Fin k ↪ α) : Fin k ≃ occupied u :=
  Equiv.ofBijective (fun i => ⟨u i,mem_occupied u i⟩)
    ⟨fun _ _ eq => u.injective (congrArg Subtype.val eq),by
      intro y
      obtain ⟨i,_,eq⟩ := Finset.mem_map.mp y.property
      exact ⟨i,Subtype.ext eq⟩⟩

theorem indexEquiv_val {k : ℕ} (u : Fin k ↪ α) (i : Fin k) : ((indexEquiv u i : occupied u) : α)=u i := rfl

end MallikDegree
