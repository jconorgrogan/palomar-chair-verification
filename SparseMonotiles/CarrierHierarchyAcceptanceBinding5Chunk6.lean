module

public import SparseMonotiles.CarrierHierarchyAcceptanceBinding5Data

@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.AcceptanceBinding5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem chunk6 : ∀ i : Fin 32,
    hierarchyAt (bindingIndex 6 i) = contactAt (bindingIndex 6 i) := by decide +kernel
end SparseMonotiles.CarrierHierarchy.AcceptanceBinding5
