import Conjectures.CircularInsertionSmallBases

/-! Canonical enumeration of perfect matchings on a finite list of vertices.
Every fixed-point-free partner involution occurs with its actual unordered
edges; this also applies when several inserted edges have equal cyclic length. -/

namespace CircularIndex.Insertion.Small

def edge (x y : ℕ) := (min x y,max x y)

theorem edge_swap (x y : ℕ) : edge x y=edge y x := by simp only [edge,Nat.min_comm,Nat.max_comm]

def represents (L : List (ℕ × ℕ)) (W : List ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ e, e∈L ↔ ∃ x∈W, e=edge x (f x)

def matchings : ℕ → List ℕ → List (List (ℕ × ℕ))
  | 0, [] => [[]]
  | 0, _::_ => []
  | _+1, [] => []
  | t+1, x::xs => xs.flatMap fun y => (matchings t (xs.erase y)).map (List.cons (edge x y))

theorem matchings_complete {t : ℕ} {W : List ℕ} {f : ℕ → ℕ}
    (hlen : W.length=2*t) (hn : W.Nodup) (hp : Partners W f) :
    ∃ L∈matchings t W, represents L W f := by
  induction t generalizing W with
  | zero =>
    have he : W=[] := List.length_eq_zero_iff.mp (by omega)
    subst W
    exact ⟨[],by simp [matchings],by simp [represents]⟩
  | succ t ih =>
    cases W with
    | nil => simp at hlen
    | cons x xs =>
      obtain ⟨hx,hxs⟩ := List.nodup_cons.mp hn
      obtain ⟨hy,hyx,hyne⟩ := hp x (List.mem_cons_self ..)
      have hym : f x∈xs := (List.mem_cons.mp hy).resolve_left hyne
      let rest := xs.erase (f x)
      have mem {z : ℕ} : z∈rest ↔ z≠f x ∧ z∈xs := hxs.mem_erase_iff
      have card : rest.length=2*t := by
        have hl := List.length_erase_add_one hym
        simp only [List.length_cons] at hlen
        dsimp only [rest]
        omega
      have incl {z : ℕ} (hz : z∈rest) : z∈x::xs := List.mem_cons_of_mem _ (mem.mp hz).2
      have partners : Partners rest f := by
        intro z hz
        obtain ⟨hz₁,hz₂⟩ := mem.mp hz
        obtain ⟨hf,hfz,hne⟩ := hp z (incl hz)
        have hzx : z≠x := fun h => hx (h ▸ hz₂)
        have hfx : f z≠x := fun h => hz₁ (hfz ▸ congrArg f h)
        have hfy : f z≠f x := fun h => hzx (hfz ▸ hyx ▸ congrArg f h)
        exact ⟨mem.mpr ⟨hfy,(List.mem_cons.mp hf).resolve_left hfx⟩,hfz,hne⟩
      obtain ⟨L,hL,desc⟩ := ih card (hxs.erase _) partners
      refine ⟨edge x (f x)::L,List.mem_flatMap.mpr ⟨f x,hym,List.mem_map.mpr ⟨L,hL,rfl⟩⟩,?_⟩
      intro e
      constructor
      · intro he
        rcases List.mem_cons.mp he with he|he
        · exact ⟨x,List.mem_cons_self ..,he⟩
        · obtain ⟨z,hz,he⟩ := (desc e).mp he
          exact ⟨z,incl hz,he⟩
      · rintro ⟨z,hz,rfl⟩
        rcases List.mem_cons.mp hz with rfl|hz
        · exact List.mem_cons_self ..
        by_cases h : z=f x
        · exact List.mem_cons.mpr (Or.inl (by rw [h,hyx,edge_swap]))
        · exact List.mem_cons_of_mem _ ((desc _).mpr ⟨z,mem.mpr ⟨h,hz⟩,rfl⟩)

end CircularIndex.Insertion.Small
