module
public import CompactCatalogBinding7Base
@[expose] public section
namespace SparseMonotiles.CompactCatalogBinding7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows2_checked : ∀ i : Fin 32, RowSame ⟨64 + i.val, by omega⟩ := by
  decide +kernel

#print axioms rows2_checked
end SparseMonotiles.CompactCatalogBinding7
