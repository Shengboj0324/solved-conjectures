import Conjectures.TransportationTables
import Conjectures.TransportationBadColumn

/-! An inadmissible pair of rows overflows exactly one small column. This
gives the Ehrhart count for every integer dilation, including dilation zero. -/

namespace TransportationEhrhart

theorem two_entries_le {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} (r : Row α k) {i j : α}
    (different : i≠j) : r.val i+r.val j≤k := by
  have one := Finset.single_le_sum (f := fun t : Other i => r.val t.val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨j,different.symm⟩ : Other i))
  exact (Nat.add_le_add_left one _).trans_eq (row_split i r)

theorem overflow_unique {m k : ℕ} (p : RowPair m k) {i j : Fin m}
    (hi : k < p.1.val (some i)+p.2.val (some i))
    (hj : k < p.1.val (some j)+p.2.val (some j)) : i=j := by
  by_contra ne
  have diff : some i≠some j := fun h => ne (Option.some.inj h)
  have a := two_entries_le p.1 diff
  have b := two_entries_le p.2 diff
  omega

noncomputable def overflowingColumn {m k : ℕ} (p : {p : RowPair m k // ¬ Admissible p}) :
    Σ j : Fin m,BadAt (some j) k := by
  classical
  have h := p.property
  unfold Admissible at h
  push Not at h
  exact ⟨h.choose,p.val,h.choose_spec⟩

theorem bad_of_overflow {m k : ℕ} (j : Fin m) (p : BadAt (some j) k) : ¬ Admissible p.val :=
  fun h => (Nat.not_lt.mpr (h j)) p.property

noncomputable def overflowEquiv (m k : ℕ) :
    {p : RowPair m k // ¬ Admissible p} ≃ Σ j : Fin m,BadAt (some j) k where
  toFun := overflowingColumn
  invFun s := ⟨s.2.val,bad_of_overflow s.1 s.2⟩
  left_inv _ := rfl
  right_inv s := by
    obtain ⟨j,p⟩ := s
    have eq := overflow_unique p.val (overflowingColumn ⟨p.val,bad_of_overflow j p⟩).2.property p.property
    apply Sigma.ext eq
    exact (Subtype.heq_iff_coe_eq (fun x => by rw [eq])).mpr rfl

theorem other_card {m : ℕ} (j : Fin m) : Fintype.card (Other (some j))=m := by
  change Fintype.card {x : Col m // ¬x=some j}=m
  rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,Fintype.card_option,Fintype.card_fin]
  omega

theorem total_pairs (m k : ℕ) : Nat.card (RowPair m k)=(k+m).choose m ^ 2 := by
  rw [Nat.card_prod,row_card,Fintype.card_option,Fintype.card_fin]
  have sz : m+1+k-1=k+m := by omega
  rw [sz,←sq]
  congr 1
  simpa using (Nat.choose_symm (n := k+m) (k := m) (by omega))

theorem good_bad_partition (m k : ℕ) : Nat.card (Table m k) +
    (∑ j : Fin m,Nat.card (BadAt (some j) k))=(k+m).choose m ^ 2 := by
  classical
  rw [Nat.card_congr (tableEquiv m k),←Nat.card_sigma,←Nat.card_congr (overflowEquiv m k),
    ←Nat.card_sum,Nat.card_congr (Equiv.sumCompl _),total_pairs]

theorem table_count_succ (m k : ℕ) : Nat.card (Table m (k+1))+
    m*(2*m+k).choose (2*m)=(k+1+m).choose m ^ 2 := by
  have p := good_bad_partition m (k+1)
  simp_rw [bad_card,other_card] at p
  have sym : (2*m+k).choose k=(2*m+k).choose (2*m) := by
    simpa using Nat.choose_symm (n := 2*m+k) (k := 2*m) (by omega)
  simpa [sym] using p

theorem table_count_zero (m : ℕ) : Nat.card (Table m 0)=1 := by
  have h := good_bad_partition m 0
  have empty (j : Fin m) : IsEmpty (BadAt (some j) 0) := ⟨fun p => by
    have a := entry_le p.val.1 (some j)
    have b := entry_le p.val.2 (some j)
    have bad := p.property
    omega⟩
  have z (j : Fin m) : Nat.card (BadAt (some j) 0)=0 := by
    let _ := empty j
    exact Nat.card_of_isEmpty
  simpa [z] using h

theorem table_count {m : ℕ} (hm : 0<m) (k : ℕ) :
    Nat.card (Table m k)=(k+m).choose m ^ 2-m*(k+2*m-1).choose (2*m) := by
  cases k with
  | zero =>
    have z : (2*m-1).choose (2*m)=0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [table_count_zero,z]
  | succ k =>
    have h := table_count_succ m k
    have e : k+1+2*m-1=2*m+k := by omega
    rw [e]
    omega

end TransportationEhrhart
