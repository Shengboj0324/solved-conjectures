import Conjectures.MonophonicPrismRoutes

namespace MonophonicProduct

set_option maxHeartbeats 2000000 in
theorem paths_20 : ∀ i : Fin 5,RouteSound ⟨20+i.val,by omega⟩ := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem coverage_20 : ∀ i : Fin 5,∀ b : Vertex,sharedMask (20+i.val) b allMasks=35184372088831 := by decide +kernel

end MonophonicProduct
