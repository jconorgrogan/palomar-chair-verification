module

public import SparseMonotiles.KeyFacetOrientation
public import SparseMonotiles.ContactCertificateDataIndexed7Base

@[expose] public section

namespace SparseMonotiles.Contact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem profile7Chunk20_checked : ∀ j : Fin 32,
    IndexedData7.geometry.ProfileValidAt 560 ⟨640 + j.val, by omega⟩ := by decide

#print axioms profile7Chunk20_checked

end SparseMonotiles.Contact
