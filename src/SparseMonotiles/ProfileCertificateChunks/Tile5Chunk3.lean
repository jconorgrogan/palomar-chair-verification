module

public import SparseMonotiles.KeyFacetOrientation
public import SparseMonotiles.ContactCertificateDataIndexed5Base

@[expose] public section

namespace SparseMonotiles.Contact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem profile5Chunk3_checked : ∀ j : Fin 32,
    IndexedData5.geometry.ProfileValidAt 80 ⟨96 + j.val, by omega⟩ := by decide

#print axioms profile5Chunk3_checked

end SparseMonotiles.Contact
