import Conjectures.MonophonicPrismRoutes

namespace MonophonicProduct

set_option maxHeartbeats 2000000 in
theorem paths_10 : ∀ i : Fin 5,RouteSound ⟨10+i.val,by omega⟩ := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem coverage_10 : ∀ i : Fin 5,∀ b : Vertex,sharedMask (10+i.val) b allMasks=35184372088831 := by decide +kernel

end MonophonicProduct
