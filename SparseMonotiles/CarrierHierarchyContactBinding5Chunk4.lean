module

public import SparseMonotiles.CarrierHierarchyContactBinding5Data

@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.ContactBinding5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem chunk4 : ∀ i : Fin 32,
    hierarchyAt (bindingIndex 4 i) = contactAt (bindingIndex 4 i) := by decide +kernel
end SparseMonotiles.CarrierHierarchy.ContactBinding5
