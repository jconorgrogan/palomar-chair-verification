module
public import Acceptance140Base
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance140Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem chunk03 : ∀ j : Fin 128, FacetChecked (tailIndex j) := by decide
#print axioms chunk03
end SparseMonotiles.Contact.Acceptance140Pilot7
