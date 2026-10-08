module

public import SparseMonotiles.KeySupportAtlas
public import SparseMonotiles.ContactCertificateDataIndexed7Base

@[expose] public section

namespace SparseMonotiles.Contact
open IndexedData7

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem atlas7Chunk8_checked : ∀ j : Fin 32,
    IndexedData7.geometry.AtlasValidAt ⟨256 + j.val, by omega⟩ := by decide

#print axioms atlas7Chunk8_checked

end SparseMonotiles.Contact
