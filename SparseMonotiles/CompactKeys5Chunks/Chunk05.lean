module

public import SparseMonotiles.CompactKeys5Data

public section
namespace SparseMonotiles.CompactBinding.Keys5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Exact rational equality of all fields for this sixteen-key block. -/
theorem chunk5 : ∀ i : Fin 16,
    compactAt (bindingIndex 5 i) = literalAt (bindingIndex 5 i) := by decide +kernel
end SparseMonotiles.CompactBinding.Keys5
