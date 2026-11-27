import Conjectures.CircularSmallInsertionWindows

/-! Consecutive classes of the general two-interval family are disjoint in every
cyclic three-class window, including windows that cross colour zero. -/

namespace CircularIndex.Insertion.Small

private def offset (g c j : ℕ) := if j=1 then 2*g+c%2 else 4*g+1

private theorem shift_numerator (g c j : ℕ) (hj : j=1 ∨ j=2) :
    ((4*g+1)*(c+j))/2=((4*g+1)*c)/2+offset g c j := by
  have par : ((4*g+1)*c)%2=c%2 := by
    rw [Nat.mul_mod,show (4*g+1)%2=1 by omega,Nat.one_mul,Nat.mod_mod]
  rcases hj with rfl|rfl <;> rw [Nat.mul_add] <;> norm_num [offset] <;> omega

private theorem move (g c j x : ℕ) (hj : j=1 ∨ j=2) :
    turn (vertexCount g) (shift g (colour g c j)) x =
      turn (vertexCount g) (shift g c) (turn (vertexCount g) (offset g c j) x) := by
  unfold turn shift colour
  rw [Nat.mul_mod_mod,Nat.mod_mul_right_div_self,Nat.mod_mul_right_div_self,shift_numerator _ _ _ hj]
  simp only [Nat.add_mod_mod,Nat.mod_add_mod]
  congr 1
  omega

theorem general_window {g k c j : ℕ} (hk₁ : 1≤k) (hk₂ : k≤2*g)
    (hj : j=1 ∨ j=2) (x : ℕ) (h : x∈classSupport g k c) :
    x∉classSupport g k (colour g c j) := by
  intro hx
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
  obtain ⟨b,hb,e⟩ := List.mem_map.mp hx
  rw [move _ _ _ _ hj] at e
  have ha' := support_lt hk₂ (show (parity c).val≤1 by have := (parity c).isLt; omega) ha
  have hb' : turn (vertexCount g) (offset g c j) b < vertexCount g :=
    Nat.mod_lt _ (by unfold vertexCount; omega)
  have eq := congrArg (unturn (vertexCount g) (shift g c)) e
  rw [unturn_turn (shift_lt g c) hb',unturn_turn (shift_lt g c) ha'] at eq
  have pe : (parity (colour g c j)).val=(c+j)%2 := Nat.mod_mod_of_dvd _ ⟨vertexCount g,rfl⟩
  simp only [support,List.mem_append,List.mem_range'_1] at ha hb
  rw [pe] at hb
  change c%2≤a ∧ a<c%2+k ∨ _ at ha
  unfold turn at eq
  have bounded (d : ℕ) (hd : d<vertexCount g) (he : (b+d)%vertexCount g=a)
      (hbnd : b<vertexCount g) : b+d=a ∨ b+d=a+vertexCount g := by
    by_cases h : b+d<vertexCount g
    · exact Or.inl ((Nat.mod_eq_of_lt h).symm.trans he)
    · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)] at he
      omega
  have bound : b<vertexCount g := by unfold vertexCount; omega
  have hd : offset g c j<vertexCount g := by unfold offset vertexCount; split <;> omega
  have cases := bounded _ hd eq bound
  rcases hj with rfl|rfl <;> norm_num [offset,vertexCount] at cases <;> omega

end CircularIndex.Insertion.Small
