import Conjectures.MallikDegreeExtendable
import Conjectures.MallikDegreeHighDeletion
import Conjectures.MallikDegreeLowDeletion
import Conjectures.MallikDegreeSimpleGraph
import Conjectures.MallikDegreeEdgeMatchings

/-! The uniform minimal counterfamily, exact gap and interval of orders. -/

namespace MallikDegree

def marked (k t : ℕ) : Finset (Fin k) := Finset.univ.filter fun i => i.val<2*k-t

theorem marked_card {k t : ℕ} (kt : k≤t) : (marked k t).card=2*k-t := by
  have hr : 2*k-t≤k := by omega
  have eq : marked k t=occupied (Fin.castLEEmb hr) := by
    ext i
    simp only [marked,Finset.mem_filter,Finset.mem_univ,true_and,occupied,Finset.mem_map]
    constructor
    · intro hi
      exact ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
    · rintro ⟨j,rfl⟩
      exact j.isLt
  rw [eq,occupied_card]

def relation (k t : ℕ) := family (L := Fin t) (marked k t)

theorem family_minimal {k t : ℕ} (hk : 3≤k) (lo : k+2≤t) (hi : t≤2*k-1) :
    Minimal (relation k t) k := by
  let D := marked k t
  have card : D.card=2*k-t := marked_card (by omega)
  have balance : D.card+t=2*k := by omega
  refine ⟨family_extendable D (by omega) (by omega) balance,?_⟩
  intro x y adj extd
  have extendsAll := extd.2.2.2
  cases x with
  | inl h =>
    cases y with
    | inl j =>
      obtain ⟨eq,mem⟩ := adj
      subst j
      exact delete_high_diagonal D h mem (by omega) balance extendsAll
    | inr l => exact delete_high_low D h l (by omega) extendsAll
  | inr l =>
    cases y with
    | inl h => exact delete_low_high D l h (by omega) extendsAll
    | inr j =>
      change l=j at adj
      subst j
      exact delete_low_diagonal D l (by omega) extendsAll

theorem exact_counts {k t : ℕ} (lo : k+2≤t) :
    Fintype.card ((Fin k ⊕ Fin t) ⊕ (Fin k ⊕ Fin t))=2*(k+t) ∧
    edges (relation k t)=2*k*t+t+(2*k-t) ∧ degreeCount (relation k t) (k+1)=2*t := by
  refine ⟨by simp; omega,?_,?_⟩
  · simpa only [relation,Fintype.card_fin,marked_card (by omega : k≤t)] using family_edges (L := Fin t) (marked k t)
  · simpa only [relation,Fintype.card_fin] using family_degree_count (L := Fin t) (marked k t)
      (by simpa only [Fintype.card_fin] using lo)

theorem exact_gap {k t : ℕ} (hk : 3≤k) (lo : k+2≤t) :
    2*((edges (relation k t) : ℝ)-2*((k : ℝ)+t)+2*k)/(2*k-1)-(degreeCount (relation k t) (k+1) : ℝ)=
      2*((2*k-t : ℕ) : ℝ)/(2*k-1) := by
  obtain ⟨_,ed,deg⟩ := exact_counts lo
  rw [ed,deg]
  push_cast
  have pos : 0<2*(k : ℝ)-1 := by
    have bound : 3≤(k : ℝ) := by exact_mod_cast hk
    linarith
  field_simp [ne_of_gt pos]
  ring

theorem violates_degree_bound {k t : ℕ} (hk : 3≤k) (lo : k+2≤t) (hi : t≤2*k-1) :
    (degreeCount (relation k t) (k+1) : ℝ)<
      2*((edges (relation k t) : ℝ)-2*((k : ℝ)+t)+2*k)/(2*k-1) := by
  obtain ⟨_,ed,deg⟩ := exact_counts lo
  rw [ed,deg]
  push_cast
  exact strict_deficit hk hi rfl

theorem all_even_orders {k n : ℕ} (hk : 3≤k) (even : Even n) (lo : 4*k+4≤n) (hi : n≤6*k-2) :
    ∃ t : ℕ,n=2*(k+t) ∧ k+2≤t ∧ t≤2*k-1 ∧ Minimal (relation k t) k ∧
      (degreeCount (relation k t) (k+1) : ℝ)<2*((edges (relation k t) : ℝ)-(n : ℝ)+2*k)/(2*k-1) := by
  obtain ⟨j,hj⟩ := even
  have ord : n=2*(k+(j-k)) := by omega
  have low : k+2≤j-k := by omega
  have high : j-k≤2*k-1 := by omega
  refine ⟨j-k,ord,low,high,family_minimal hk low high,?_⟩
  have cast : (n : ℝ)=2*((k : ℝ)+((j-k : ℕ) : ℝ)) := by exact_mod_cast ord
  rw [cast]
  exact violates_degree_bound hk low high

theorem order_sixteen :
    Minimal (relation 3 5) 3 ∧ edges (relation 3 5)=36 ∧ degreeCount (relation 3 5) 4=10 ∧
      (degreeCount (relation 3 5) 4 : ℝ)<52/5 := by
  obtain ⟨_,ed,deg⟩ := exact_counts (k := 3) (t := 5) (by decide)
  exact ⟨family_minimal (by decide) (by decide) (by decide),ed,deg,by rw [deg]; norm_num⟩

end MallikDegree
