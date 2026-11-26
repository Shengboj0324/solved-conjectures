import Conjectures.FiscusGridTable

/-! All 16,384 local minimax equations are reduced by the stock kernel, in
eight groups. The final theorem recovers any individual equation by division. -/

namespace FiscusGrid

private def checkedGroup (g : ℕ) : Bool :=
  (List.range 8).all fun i => checkedBlock (8*g+i)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem all_groups : ∀ g : Fin 8, checkedGroup g.val=true := by
  intro g
  fin_cases g <;> decide

theorem certificate (s : ℕ) (hs : s<2^14) : consistent s=true := by
  have m : s<16384 := hs
  let b := s/256
  let g := b/8
  have hg : g<8 := by dsimp [g,b]; omega
  have h := all_groups ⟨g,hg⟩
  simp only [checkedGroup,List.all_eq_true,List.mem_range] at h
  have blk := h (b%8) (Nat.mod_lt _ (by decide))
  have idx : 8*g+b%8=b := by dsimp [g]; omega
  rw [idx] at blk
  simp only [checkedBlock,List.all_eq_true,List.mem_range] at blk
  have v := blk (s%256) (Nat.mod_lt _ (by decide))
  have idx' : 256*b+s%256=s := by dsimp [b]; omega
  rwa [idx'] at v

end FiscusGrid
