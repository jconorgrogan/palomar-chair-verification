module
public import Acceptance17Base
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance17Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem chunk01 : ∀ j : Fin 256, FacetChecked (chunkIndex 1 j) := by decide
#print axioms chunk01
end SparseMonotiles.Contact.Acceptance17Pilot7
