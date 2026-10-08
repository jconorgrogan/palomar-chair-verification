module
public import Acceptance76Base
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance76Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem chunk02 : ∀ j : Fin 256, FacetChecked (chunkIndex 2 j) := by decide
#print axioms chunk02
end SparseMonotiles.Contact.Acceptance76Pilot7
