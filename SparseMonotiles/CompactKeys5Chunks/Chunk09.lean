module

public import SparseMonotiles.CompactKeys5Data

public section
namespace SparseMonotiles.CompactBinding.Keys5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Exact rational equality of all fields for this sixteen-key block. -/
theorem chunk9 : ∀ i : Fin 16,
    compactAt (bindingIndex 9 i) = literalAt (bindingIndex 9 i) := by decide +kernel
end SparseMonotiles.CompactBinding.Keys5
