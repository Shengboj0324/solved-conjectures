import Conjectures.MonophonicPrismRoutes

namespace MonophonicProduct

set_option maxHeartbeats 2000000 in
theorem paths_35 : ∀ i : Fin 5,RouteSound ⟨35+i.val,by omega⟩ := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem coverage_35 : ∀ i : Fin 5,∀ b : Vertex,sharedMask (35+i.val) b allMasks=35184372088831 := by decide +kernel

end MonophonicProduct
