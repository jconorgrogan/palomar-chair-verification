module

public import SparseMonotiles.FacetAtlasCompleteness5Data

@[expose] public section
namespace SparseMonotiles.Contact.FacetAtlasCompleteness5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem axis0_checked : ∀ (b : Fin 5 → Bool) (positive : Bool),
    FacetLookupCompleteAt IndexedData5.geometry lookup b 0 positive := by decide +kernel
#print axioms axis0_checked
end SparseMonotiles.Contact.FacetAtlasCompleteness5
