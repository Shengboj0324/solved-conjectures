import Conjectures.MonophonicPrismIncidence

/-! The subdivision stars are monophonic sets. Every other color class in
the displayed upper colorings has at most two vertices. -/

namespace MonophonicProduct

theorem center_of_internal {n : ℕ} {p : Fin n → Vertex} (hp : InducedPath witnessGraph p)
    {s : Fin 18} {i : Fin n} (hi : p i∈star s) (left : 0 < i.val) (right : i.val+1 < n) :
    ∃ j : Fin n,p j=original s := by
  let a : Fin n := ⟨i.val-1,by omega⟩
  let b : Fin n := ⟨i.val+1,right⟩
  have ha : witnessGraph.Adj (p i) (p a) := (hp.2 i a).2 (Or.inr (by dsimp [a]; omega))
  have hb : witnessGraph.Adj (p i) (p b) := (hp.2 i b).2 (Or.inl rfl)
  have ne : p a≠p b := by
    intro eq
    have bad:=congrArg Fin.val (hp.1 a b eq)
    dsimp [a,b] at bad
    omega
  rcases subdivision_neighbors s (p i) hi _ _ ha hb ne with h | h
  · exact ⟨a,h⟩
  · exact ⟨b,h⟩

theorem no_three_in_star {n : ℕ} {p : Fin n → Vertex} (hp : InducedPath witnessGraph p)
    {s : Fin 18} {i j k : Fin n} (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (si : p i∈star s) (sj : p j∈star s) (sk : p k∈star s) : False := by
  have dij : i.val≠j.val := fun e => ij (Fin.ext e)
  have dik : i.val≠k.val := fun e => ik (Fin.ext e)
  have djk : j.val≠k.val := fun e => jk (Fin.ext e)
  have interior : (0 < i.val ∧ i.val+1 < n) ∨ (0 < j.val ∧ j.val+1 < n) ∨ (0 < k.val ∧ k.val+1 < n) := by omega
  have existsCenter : ∃ a : Fin n,p a=original s := by
    rcases interior with h | h | h
    · exact center_of_internal hp si h.1 h.2
    · exact center_of_internal hp sj h.1 h.2
    · exact center_of_internal hp sk h.1 h.2
  obtain ⟨a,ha⟩:=existsCenter
  have near (b : Fin n) (hb : p b∈star s) : consecutive a b := by
    apply (hp.2 a b).1
    rw [ha]
    exact (mem_star s _).1 hb
  have x:=near i si
  have y:=near j sj
  have z:=near k sk
  unfold consecutive at x y z
  omega

theorem small_fiber_excludes {k n : ℕ} {G : SimpleGraph Vertex} {p : Fin n → Vertex}
    (hp : InducedPath G p) {col : Vertex → Fin k} {i j l : Fin n}
    (ij : i≠j) (il : i≠l) (jl : j≠l) (eqj : col (p i)=col (p j)) (eql : col (p i)=col (p l))
    (small : (fiber col (col (p i))).card≤2) : False := by
  have larger : 2<(fiber col (col (p i))).card := Finset.two_lt_card_iff.mpr
    ⟨p i,p j,p l,(mem_fiber ..).2 rfl,
      (mem_fiber ..).2 eqj.symm,(mem_fiber ..).2 eql.symm,fun e => ij (hp.1 _ _ e),
      fun e => il (hp.1 _ _ e),fun e => jl (hp.1 _ _ e)⟩
  omega

theorem primal_valid : ValidColoring witnessGraph primal := by
  refine ⟨primal_proper,?_⟩
  intro n p hp i j l ij il jl eqj eql
  rcases primal_fibers (primal (p i)) with small | ⟨s,subset⟩
  · exact small_fiber_excludes hp ij il jl eqj eql small
  · exact no_three_in_star hp ij il jl (subset ((mem_fiber ..).2 rfl))
      (subset ((mem_fiber ..).2 eqj.symm)) (subset ((mem_fiber ..).2 eql.symm))

theorem dual_valid : ValidColoring witnessGraphᶜ dual := by
  refine ⟨dual_proper,?_⟩
  intro n p hp i j l ij il jl eqj eql
  exact small_fiber_excludes hp ij il jl eqj eql (dual_fibers _)

theorem dual_exact : ChromaticNumber witnessGraphᶜ 27 := ⟨⟨dual,dual_valid⟩,fun _ ⟨_,h⟩ => dual_lower h⟩

end MonophonicProduct
