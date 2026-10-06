module

public import SparseMonotiles.ContactKeyCodeData5

@[expose] public section

namespace SparseMonotiles.Contact
open IndexedData5

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keyCode5Chunk03_checked : ∀ j : Fin 32,
    geometry.CodeValidAt coordinateCode ⟨96 + j.val, by omega⟩ := by decide +kernel

#print axioms keyCode5Chunk03_checked
end SparseMonotiles.Contact
