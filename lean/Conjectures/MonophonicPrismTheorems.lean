import Conjectures.MonophonicPrismIsomorphism
import Conjectures.MonophonicPrismCounterexample

/-! Exact counts for the first member of the prism family, with the
complement count and the order proved for every member. -/

namespace MonophonicProduct

theorem expanded_prism_counterexample :
    Fintype.card (PrismVertex 3)=45 ∧ ChromaticNumber (subdivision 3) 20 ∧
    ChromaticNumber (subdivision 3)ᶜ 27 ∧
    ((Fintype.card (PrismVertex 3)+1 : ℝ)/2)^2<(20 : ℝ)*27 := by
  refine ⟨vertex_count 3,number_pullback prismIso primal_exact,family_dual_exact 3,?_⟩
  rw [vertex_count]
  norm_num

theorem expanded_prism_complements (s : ℕ) :
    Fintype.card (PrismVertex s)=15*s ∧ ChromaticNumber (subdivision s)ᶜ (9*s) :=
  ⟨vertex_count s,family_dual_exact s⟩

end MonophonicProduct
