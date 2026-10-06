module

public import SparseMonotiles.KeySupportAtlas
public import SparseMonotiles.ContactCertificateDataIndexed5Base

@[expose] public section

namespace SparseMonotiles.Contact
open IndexedData5

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem atlas5Chunk0_checked : ∀ j : Fin 32,
    IndexedData5.geometry.AtlasValidAt ⟨0 + j.val, by omega⟩ := by decide

#print axioms atlas5Chunk0_checked

end SparseMonotiles.Contact
