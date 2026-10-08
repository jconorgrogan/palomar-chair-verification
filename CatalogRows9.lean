module
public import CompactCatalogBinding7Base
@[expose] public section
namespace SparseMonotiles.CompactCatalogBinding7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows9_checked : ∀ i : Fin 32, RowSame ⟨288 + i.val, by omega⟩ := by
  decide +kernel

#print axioms rows9_checked
end SparseMonotiles.CompactCatalogBinding7
