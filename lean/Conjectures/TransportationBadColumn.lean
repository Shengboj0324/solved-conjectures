import Conjectures.TransportationRows

/-! Counting the pairs of rows that overflow one specified column. -/

namespace TransportationEhrhart

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Other (j : α) := {x : α // x ≠ j}
abbrev BadAt (j : α) (k : ℕ) :=
  {p : Row α k × Row α k // k < p.1.val j+p.2.val j}

def away (j : α) (v : α → ℕ) := ∑ i : Other j,v i

theorem row_split {k : ℕ} (j : α) (v : Row α k) : v.val j+away j v.val=k :=
  (sum_away j v.val).symm.trans v.property

def packOthers (j : α) (p : (α → ℕ) × (α → ℕ)) : Other j ⊕ Other j → ℕ :=
  Sum.elim (fun i => p.1 i) (fun i => p.2 i)

theorem packOthers_sum (j : α) (v w : α → ℕ) :
    ∑ i,packOthers j (v,w) i=away j v+away j w := by
  rw [Fintype.sum_sum_type]
  rfl

def restoreRow (j : α) (k : ℕ) (v : Other j → ℕ) (mass : ∑ i,v i ≤ k) : Row α k :=
  ⟨insertAt j (k-∑ i,v i) v,by rw [sum_insertAt,Nat.sub_add_cancel mass]⟩

@[simp] theorem restoreRow_at (j : α) (k : ℕ) (v : Other j → ℕ) (mass) :
    (restoreRow j k v mass).val j=k-∑ i,v i := insertAt_self _ _ _

@[simp] theorem restoreRow_other (j : α) (k : ℕ) (v : Other j → ℕ) (mass) (i : Other j) :
    (restoreRow j k v mass).val i=v i := insertAt_other _ _ _ _

def badToOthers (j : α) (k : ℕ) (p : BadAt j (k+1)) : AtMost (Other j ⊕ Other j) k :=
  ⟨packOthers j (p.val.1.val,p.val.2.val),by
    rw [packOthers_sum]
    have x := row_split j p.val.1
    have y := row_split j p.val.2
    have bad := p.property
    omega⟩

def othersToBad (j : α) (k : ℕ) (v : AtMost (Other j ⊕ Other j) k) : BadAt j (k+1) := by
  let a (i : Other j) := v.val (.inl i)
  let b (i : Other j) := v.val (.inr i)
  have h := v.property
  rw [Fintype.sum_sum_type] at h
  change (∑ i,a i)+(∑ i,b i)≤k at h
  refine ⟨(restoreRow j (k+1) a (by omega),restoreRow j (k+1) b (by omega)),?_⟩
  simp only [restoreRow_at]
  omega

theorem restore_from_row {k : ℕ} (j : α) (v : Row α k) (h : ∑ i : Other j,v.val i ≤ k) :
    restoreRow j k (fun i : Other j => v.val i) h=v := by
  apply Subtype.ext
  funext i
  by_cases eq : i=j
  · subst i
    rw [restoreRow_at]
    have s := row_split j v
    unfold away at s
    omega
  · exact restoreRow_other j k _ h ⟨i,eq⟩

def badEquiv (j : α) (k : ℕ) : BadAt j (k+1) ≃ AtMost (Other j ⊕ Other j) k where
  toFun := badToOthers j k
  invFun := othersToBad j k
  left_inv p := by
    apply Subtype.ext
    have bound (v : Row α (k+1)) : ∑ i : Other j,v.val i ≤ k+1 := by
      have h := row_split j v
      unfold away at h
      omega
    exact Prod.ext (restore_from_row j p.val.1 (bound _)) (restore_from_row j p.val.2 (bound _))
  right_inv v := by
    apply Subtype.ext
    funext i
    cases i with
    | inl i => simp [badToOthers, packOthers, othersToBad, restoreRow, insertAt, i.property]
    | inr i => simp [badToOthers, packOthers, othersToBad, restoreRow, insertAt, i.property]

theorem bad_card (j : α) (k : ℕ) :
    Nat.card (BadAt j (k+1))=(2*Fintype.card (Other j)+k).choose k := by
  rw [Nat.card_congr (badEquiv j k),atMost_card,Fintype.card_sum,two_mul]

end TransportationEhrhart
