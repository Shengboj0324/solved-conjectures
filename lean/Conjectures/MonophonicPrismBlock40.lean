import Conjectures.MonophonicPrismRoutes

namespace MonophonicProduct

set_option maxHeartbeats 2000000 in
theorem paths_40 : ∀ i : Fin 5,RouteSound ⟨40+i.val,by omega⟩ := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem coverage_40 : ∀ i : Fin 5,∀ b : Vertex,sharedMask (40+i.val) b allMasks=35184372088831 := by decide +kernel

end MonophonicProduct
