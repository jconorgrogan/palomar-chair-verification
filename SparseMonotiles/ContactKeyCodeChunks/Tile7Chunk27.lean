module

public import SparseMonotiles.ContactKeyCodeData7

@[expose] public section

namespace SparseMonotiles.Contact
open IndexedData7

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keyCode7Chunk27_checked : ∀ j : Fin 32,
    geometry.CodeValidAt coordinateCode ⟨864 + j.val, by omega⟩ := by decide +kernel

#print axioms keyCode7Chunk27_checked
end SparseMonotiles.Contact
