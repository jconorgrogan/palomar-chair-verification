module

public import SparseMonotiles.CarrierHierarchyAcceptanceBinding5Data

@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.AcceptanceBinding5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem chunk5 : ∀ i : Fin 32,
    hierarchyAt (bindingIndex 5 i) = contactAt (bindingIndex 5 i) := by decide +kernel
end SparseMonotiles.CarrierHierarchy.AcceptanceBinding5
