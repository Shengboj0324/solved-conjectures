import Conjectures.LonelinessFourSpeedEnumeration
import Conjectures.LonelinessModularRationalWitness
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin

/-! Finite residue tables at the exact threshold `num/den`. A row is accepted
only when it appears in the retained table or has a checked modular witness.
The complete finite support enumeration supplies the coverage proof. -/

namespace Loneliness.Modular.FourSpeed

def coveredSupports (m r : ℕ) (inv : ℕ → ℕ) : Finset (Finset ℕ) :=
  if r=1 then boundedSupports m r else normalizedSupports m r inv

def rowCheck (num den m : ℕ) (retained : Finset (Finset ℕ)) (s : Finset ℕ) : Bool :=
  decide (s∈retained ∨ ∃ t∈Finset.range m, ∀ d∈s, num*m≤den*folded m (t*d))

def residueCheck (num den m r : ℕ) (inv : ℕ → ℕ)
    (retained : Finset (Finset ℕ)) : Bool :=
  decide (∀ s∈coveredSupports m r inv, rowCheck num den m retained s=true)

/-- A residue table of row size other than one can be checked in pieces. Each piece
filters the bounded supports by the sum of their entries modulo `n`, so a kernel
decision handles only part of the rows. -/
theorem residueCheck_of_sum_chunks {num den m r : ℕ} {inv : ℕ → ℕ}
    {retained : Finset (Finset ℕ)} (hr : r≠1) (n : ℕ) (hn : 0<n)
    (h : ∀ i<n, ∀ s∈(boundedSupports m r).filter (fun s => s.sum id % n=i),
      PairNormalized m inv s → rowCheck num den m retained s=true) :
    residueCheck num den m r inv retained=true := by
  unfold residueCheck coveredSupports normalizedSupports
  rw [if_neg hr]
  apply decide_eq_true
  intro s hs
  obtain ⟨hb,hp⟩ := Finset.mem_filter.mp hs
  exact h _ (Nat.mod_lt _ hn) s (Finset.mem_filter.mpr ⟨hb,rfl⟩) hp

theorem rowCheck_sound {num den m : ℕ} {retained : Finset (Finset ℕ)} {s : Finset ℕ}
    (h : rowCheck num den m retained s=true) :
    s∈retained ∨ HasRationalWitness num den m (s.sort (·≤·)) := by
  rcases of_decide_eq_true h with hmem | ⟨t,_ht,hw⟩
  · exact Or.inl hmem
  · refine Or.inr ⟨t,?_⟩
    intro d hd
    exact hw d ((Finset.mem_sort (·≤·)).mp hd)

theorem coveredSupports_complete {m r : ℕ} (hm : 2≤m) (hr : 0<r)
    (inv : ℕ → ℕ) (hinv : ∀ a, 0<a → 2*a≤m → (a*inv a)%m=1%m)
    (s : Finset ℕ) (hs : FoldedSupport m s) (hcard : s.card=r) :
    ∃ u v : ℕ, (u*v)%m=1%m ∧ foldedSupport m u s∈coveredSupports m r inv := by
  by_cases hr1 : r=1
  · rw [hr1] at hcard ⊢
    obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp hcard
    have ha := hs a (by simp)
    have hunit : (inv a*a)%m=1%m := by simpa only [Nat.mul_comm] using hinv a ha.1 ha.2
    refine ⟨inv a,a,hunit,?_⟩
    have he : foldedSupport m (inv a) {a}={1} := by
      simp only [foldedSupport,Finset.image_singleton]
      congr 1
      exact (folded_eq_of_mod_eq hunit).trans (folded_one hm)
    rw [he]
    simp only [coveredSupports,ite_true]
    apply mem_boundedSupports_iff.mpr
    refine ⟨?_,by simp,by simp⟩
    intro x hx
    have hx1 : x=1 := Finset.mem_singleton.mp hx
    subst x
    exact ⟨by omega,by omega⟩
  · simpa only [coveredSupports,ite_eq_right hr1] using
      normalizedSupports_complete hm (by omega : 2≤r) inv hinv s hs hcard

def residueSupport (m : ℕ) (ds : List ℕ) : Finset ℕ :=
  (ds.map (folded m)).toFinset

theorem residueSupport_valid {m : ℕ} (hm : 0<m) (ds : List ℕ)
    (hmod : ∀ d∈ds, d%m≠0) : FoldedSupport m (residueSupport m ds) := by
  intro a ha
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hne : folded m d≠0 := fun h => hmod d hd ((folded_eq_zero_iff hm).mp h)
  exact ⟨Nat.pos_of_ne_zero hne,folded_le_half m d⟩

theorem residueSupport_card_pos {m : ℕ} {ds : List ℕ} (hne : ds≠[]) :
    0<(residueSupport m ds).card := by
  apply Finset.card_pos.mpr
  obtain ⟨d,hd⟩ := List.exists_mem_of_ne_nil ds hne
  exact ⟨folded m d,List.mem_toFinset.mpr (List.mem_map.mpr ⟨d,hd,rfl⟩)⟩

theorem residueSupport_card_le (m : ℕ) (ds : List ℕ) :
    (residueSupport m ds).card≤ds.length := by
  simpa only [residueSupport,List.length_map] using List.toFinset_card_le (ds.map (folded m))

theorem transformed_support_eq (m u : ℕ) (hm : 0<m) (ds : List ℕ) :
    foldedSupport m u (residueSupport m ds)=
      (ds.map (fun d => folded m (u*d))).toFinset := by
  ext a
  simp only [foldedSupport,residueSupport,Finset.mem_image,List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨b,⟨d,hd,rfl⟩,he⟩
    exact ⟨d,hd,(folded_mul_folded m d u hm).symm.trans he⟩
  · rintro ⟨d,hd,he⟩
    exact ⟨folded m d,⟨d,hd,rfl⟩,(folded_mul_folded m d u hm).trans he⟩

theorem transformed_support_witness {num den m u v : ℕ} (hm : 0<m)
    (hunit : (u*v)%m=1%m) (ds : List ℕ)
    (hw : HasRationalWitness num den m
      ((foldedSupport m u (residueSupport m ds)).sort (·≤·))) :
    HasRationalWitness num den m ds := by
  have hmem (d : ℕ) : d∈(foldedSupport m u (residueSupport m ds)).sort (·≤·) ↔
      d∈ds.map (fun a => folded m (u*a)) := by
    rw [Finset.mem_sort,transformed_support_eq m u hm ds,List.mem_toFinset]
  obtain ⟨t,ht⟩ := hw
  apply (hasRationalWitness_folded_unit hm hunit ds).mp
  exact ⟨t,(rationalWitness_of_mem_equiv hmem).mp ht⟩

/-- Every low-value list of at most four speeds, all nonzero modulo `m`,
has a unit-normalized folded support in the explicitly retained table.
Repeated folded residues are covered by the certificates at smaller sizes. -/
theorem checked_residue_cover {num den m : ℕ} (hden : 0<den) (hhalf : 2*num≤den)
    (hm : 2≤m) (inv : ℕ → ℕ)
    (hinv : ∀ a, 0<a → 2*a≤m → (a*inv a)%m=1%m)
    (retained : Finset (Finset ℕ))
    (hcheck : ∀ r, 0<r → r≤4 → residueCheck num den m r inv retained=true)
    (ds : List ℕ) (hne : ds≠[]) (hlen : ds.length≤4)
    (hmod : ∀ d∈ds, d%m≠0) (hlow : value ds<(num : ℝ)/den) :
    ∃ u v : ℕ, (u*v)%m=1%m ∧ foldedSupport m u (residueSupport m ds)∈retained := by
  have hmpos : 0<m := by omega
  have hs := residueSupport_valid hmpos ds hmod
  have hcardpos := residueSupport_card_pos (m:=m) hne
  have hcardbound := (residueSupport_card_le m ds).trans hlen
  obtain ⟨u,v,hunit,hmem⟩ := coveredSupports_complete hm hcardpos inv hinv
    (residueSupport m ds) hs rfl
  have hc := hcheck _ hcardpos hcardbound
  have hrow : rowCheck num den m retained (foldedSupport m u (residueSupport m ds))=true :=
    (of_decide_eq_true hc) _ hmem
  rcases rowCheck_sound hrow with hretained | hw
  · exact ⟨u,v,hunit,hretained⟩
  · have hwds := transformed_support_witness hmpos hunit ds hw
    exact False.elim ((not_le_of_gt hlow)
      (hasRationalWitness_value_lower hden hhalf hmpos hwds))

theorem reindex_of_range_cover {n : ℕ} (f g : Fin n → ℕ)
    (hg : Function.Injective g) (hcover : ∀ i, ∃ j, f j=g i) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, f (σ i)=g i := by
  classical
  choose choice hchoice using hcover
  have hinj : Function.Injective choice := by
    intro i j hij
    apply hg
    rw [←hchoice i,←hchoice j,hij]
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective choice
    ((Fintype.bijective_iff_injective_and_card choice).mpr ⟨hinj,rfl⟩)
  exact ⟨σ,hchoice⟩

/-- A retained support enumerated by distinct root coordinates gives an
actual coordinate permutation, not merely equality of sets. This permits
the finite lift tree to start from the listed increasing root tuple. -/
theorem retained_support_reindex {n m u : ℕ} (hm : 0<m)
    (v root : Fin n → ℕ) (hroot : Function.Injective root)
    (hsupport : (List.ofFn root).toFinset=
      foldedSupport m u (residueSupport m (List.ofFn v))) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, folded m (u*v (σ i))=root i := by
  apply reindex_of_range_cover (fun i => folded m (u*v i)) root hroot
  intro i
  have hmem : root i∈foldedSupport m u (residueSupport m (List.ofFn v)) := by
    rw [←hsupport]
    exact List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩)
  rw [transformed_support_eq m u hm (List.ofFn v)] at hmem
  obtain ⟨a,ha,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hmem)
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
  exact ⟨j,he⟩

end Loneliness.Modular.FourSpeed
