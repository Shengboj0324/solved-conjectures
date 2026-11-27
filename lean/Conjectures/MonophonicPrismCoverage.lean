import Conjectures.MonophonicPrismBlock00
import Conjectures.MonophonicPrismBlock05
import Conjectures.MonophonicPrismBlock10
import Conjectures.MonophonicPrismBlock15
import Conjectures.MonophonicPrismBlock20
import Conjectures.MonophonicPrismBlock25
import Conjectures.MonophonicPrismBlock30
import Conjectures.MonophonicPrismBlock35
import Conjectures.MonophonicPrismBlock40

/-! The 45 checked induced paths cover every triple except possibly a common
subdivision star. The bitwise certificates are translated to actual vertices. -/

namespace MonophonicProduct

theorem routes_sound (i : Fin 45) : RouteSound i := by
  fin_cases i
  · exact paths_00 0
  · exact paths_00 1
  · exact paths_00 2
  · exact paths_00 3
  · exact paths_00 4
  · exact paths_05 0
  · exact paths_05 1
  · exact paths_05 2
  · exact paths_05 3
  · exact paths_05 4
  · exact paths_10 0
  · exact paths_10 1
  · exact paths_10 2
  · exact paths_10 3
  · exact paths_10 4
  · exact paths_15 0
  · exact paths_15 1
  · exact paths_15 2
  · exact paths_15 3
  · exact paths_15 4
  · exact paths_20 0
  · exact paths_20 1
  · exact paths_20 2
  · exact paths_20 3
  · exact paths_20 4
  · exact paths_25 0
  · exact paths_25 1
  · exact paths_25 2
  · exact paths_25 3
  · exact paths_25 4
  · exact paths_30 0
  · exact paths_30 1
  · exact paths_30 2
  · exact paths_30 3
  · exact paths_30 4
  · exact paths_35 0
  · exact paths_35 1
  · exact paths_35 2
  · exact paths_35 3
  · exact paths_35 4
  · exact paths_40 0
  · exact paths_40 1
  · exact paths_40 2
  · exact paths_40 3
  · exact paths_40 4

theorem all_pairs_covered (a b : Vertex) : sharedMask a b allMasks=35184372088831 := by
  fin_cases a
  · exact coverage_00 0 b
  · exact coverage_00 1 b
  · exact coverage_00 2 b
  · exact coverage_00 3 b
  · exact coverage_00 4 b
  · exact coverage_05 0 b
  · exact coverage_05 1 b
  · exact coverage_05 2 b
  · exact coverage_05 3 b
  · exact coverage_05 4 b
  · exact coverage_10 0 b
  · exact coverage_10 1 b
  · exact coverage_10 2 b
  · exact coverage_10 3 b
  · exact coverage_10 4 b
  · exact coverage_15 0 b
  · exact coverage_15 1 b
  · exact coverage_15 2 b
  · exact coverage_15 3 b
  · exact coverage_15 4 b
  · exact coverage_20 0 b
  · exact coverage_20 1 b
  · exact coverage_20 2 b
  · exact coverage_20 3 b
  · exact coverage_20 4 b
  · exact coverage_25 0 b
  · exact coverage_25 1 b
  · exact coverage_25 2 b
  · exact coverage_25 3 b
  · exact coverage_25 4 b
  · exact coverage_30 0 b
  · exact coverage_30 1 b
  · exact coverage_30 2 b
  · exact coverage_30 3 b
  · exact coverage_30 4 b
  · exact coverage_35 0 b
  · exact coverage_35 1 b
  · exact coverage_35 2 b
  · exact coverage_35 3 b
  · exact coverage_35 4 b
  · exact coverage_40 0 b
  · exact coverage_40 1 b
  · exact coverage_40 2 b
  · exact coverage_40 3 b
  · exact coverage_40 4 b

theorem full_bits : ∀ c : Vertex,(35184372088831 : ℕ).testBit c=true := by decide +kernel

theorem triple_support (a b c : Vertex) :
    (∃ i : Fin 45,a∈route i ∧ b∈route i ∧ c∈route i) ∨
    (∃ s : Fin 18,a∈star s ∧ b∈star s ∧ c∈star s) := by
  have covered : (sharedMask a b allMasks).testBit c=true := by rw [all_pairs_covered,full_bits]
  obtain ⟨mask,member,ha,hb,hc⟩ := (sharedMask_mem _ _ _ _).1 covered
  rcases List.mem_append.mp member with left | right
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp left
    exact Or.inl ⟨i,((routes_sound i).2 a).1 ha,((routes_sound i).2 b).1 hb,((routes_sound i).2 c).1 hc⟩
  · obtain ⟨s,_,rfl⟩:=List.mem_map.mp right
    exact Or.inr ⟨s,(mem_star s a).2 ha,(mem_star s b).2 hb,(mem_star s c).2 hc⟩

theorem monochrome_triple {k : ℕ} {col : Vertex → Fin k} (valid : ValidColoring witnessGraph col)
    {a b c : Vertex} (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (same1 : col a=col b) (same2 : col a=col c) : ∃ s : Fin 18,a∈star s ∧ b∈star s ∧ c∈star s := by
  rcases triple_support a b c with ⟨u,ha,hb,hc⟩ | h
  · obtain ⟨i,rfl⟩:=List.mem_iff_get.mp ha
    obtain ⟨j,rfl⟩:=List.mem_iff_get.mp hb
    obtain ⟨l,rfl⟩:=List.mem_iff_get.mp hc
    exact False.elim (valid.monophonic (route u).get (routes_sound u).1 i j l
      (fun e => ab (congrArg _ e)) (fun e => ac (congrArg _ e)) (fun e => bc (congrArg _ e)) same1 same2)
  · exact h

end MonophonicProduct
