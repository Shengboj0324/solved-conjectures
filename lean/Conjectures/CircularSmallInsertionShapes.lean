import Conjectures.CircularSmallInsertionFamily

/-! A finite set of vertices is encoded by its membership bits. The interval,
translation and reflection functions use the actual vertex labels modulo n. -/

namespace CircularIndex.Insertion.Small.Shapes

def segment (n s a : ℕ) := lengthMask ((List.range a).map (fun i => (s+i)%n))
def vertices (n W : ℕ) := (List.range n).filter W.testBit
def translate (n t W : ℕ) := lengthMask ((vertices n W).map (fun x => (x+t)%n))
def reflect (n t W : ℕ) := lengthMask ((vertices n W).map (fun x => (t+n-x)%n))

theorem segment_mem (n s a x : ℕ) : (segment n s a).testBit x=true ↔
    ∃ i<a, (s+i)%n=x := by simp [segment,lengthMask_mem]

theorem translate_mem (n t W y : ℕ) : (translate n t W).testBit y=true ↔
    ∃ x, (x<n ∧ W.testBit x=true) ∧ (x+t)%n=y := by simp [translate,vertices,lengthMask_mem]

theorem reflect_mem (n t W y : ℕ) : (reflect n t W).testBit y=true ↔
    ∃ x, (x<n ∧ W.testBit x=true) ∧ (t+n-x)%n=y := by simp [reflect,vertices,lengthMask_mem]

theorem disjoint_iff (A B : ℕ) : A &&& B=0 ↔ ∀ x, A.testBit x=true → B.testBit x=false := by
  constructor
  · intro h x ha
    have e := congrArg (fun a : ℕ => a.testBit x) h
    simpa [Nat.testBit_and,ha] using e
  · intro h
    apply Nat.eq_of_testBit_eq
    intro x
    cases ha : A.testBit x <;> simp [Nat.testBit_and,ha,h]

/-- Two disjoint cyclic runs of total length 2g. The second run may be empty. -/
def TwoIntervals (g W : ℕ) : Prop :=
  ∃ s<vertexCount g, ∃ a, 1≤a ∧ a≤2*g ∧ ∃ t<vertexCount g,
    let A := segment (vertexCount g) s a
    let B := segment (vertexCount g) t (2*g-a)
    A &&& B=0 ∧ W=A ||| B

structure WindowConditions (g A B : ℕ) : Prop where
  self₀ : A &&& translate (vertexCount g) (2*g) A=0
  self₁ : B &&& translate (vertexCount g) (2*g) B=0
  cross₀ : A &&& translate (vertexCount g) (2*g) B=0
  cross₁ : B &&& translate (vertexCount g) (2*g+1) A=0

def atStart (g s : ℕ) : List ℕ :=
  ((List.range (2*g)).flatMap fun i =>
    (List.range (vertexCount g)).filterMap fun t =>
      let A := segment (vertexCount g) s (i+1)
      let B := segment (vertexCount g) t (2*g-(i+1))
      let W := A ||| B
      if A &&& B=0 ∧ W &&& translate (vertexCount g) (2*g) W=0 then some W else none).eraseDups

def allSupports (g : ℕ) :=
  ((List.finRange (vertexCount g)).flatMap (fun s => atStart g s.val)).eraseDups

theorem supports_complete {g W : ℕ} (shape : TwoIntervals g W)
    (self : W &&& translate (vertexCount g) (2*g) W=0) : W∈allSupports g := by
  obtain ⟨s,hs,a,ha,hb,t,ht,dis,defW⟩ := shape
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show a≠0 by omega)
  subst W
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  refine ⟨⟨s,hs⟩,List.mem_finRange _,List.mem_eraseDups.mpr (List.mem_flatMap.mpr ?_)⟩
  exact ⟨i,List.mem_range.mpr (by omega),List.mem_filterMap.mpr
    ⟨t,List.mem_range.mpr ht,ite_eq_left ⟨dis,self⟩⟩⟩

def normalized (g A : ℕ) := A.testBit 0 && !(A.testBit (vertexCount g-1))

def windowPairs (g : ℕ) : List (ℕ × ℕ) :=
  let all := allSupports g
  (all.filter (normalized g)).flatMap fun A =>
    (all.filter (fun B => decide (A &&& translate (vertexCount g) (2*g) B=0 ∧
      B &&& translate (vertexCount g) (2*g+1) A=0))).map (fun B => (A,B))

theorem pairs_complete {g A B : ℕ} (sha : TwoIntervals g A) (shb : TwoIntervals g B)
    (start : normalized g A=true) (h : WindowConditions g A B) : (A,B)∈windowPairs g := by
  apply List.mem_flatMap.mpr
  refine ⟨A,List.mem_filter.mpr ⟨supports_complete sha h.self₀,start⟩,?_⟩
  exact List.mem_map.mpr ⟨B,List.mem_filter.mpr ⟨supports_complete shb h.self₁,
    decide_eq_true ⟨h.cross₀,h.cross₁⟩⟩,rfl⟩

def model (g k ε : ℕ) := lengthMask (support g k ε)

def Equivalent (g A B : ℕ) : Prop :=
  ∃ i : Fin (2*g), let k := i.val+1
    (A=model g k 0 ∧ B=model g k 1) ∨ ∃ t : Fin (vertexCount g),
      reflect (vertexCount g) t.val A=model g k 0 ∧
      reflect (vertexCount g) (1+t.val) B=model g k 1

instance (g A B : ℕ) : Decidable (Equivalent g A B) := by unfold Equivalent; infer_instance

end CircularIndex.Insertion.Small.Shapes
