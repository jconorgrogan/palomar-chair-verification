module
public import CompactCatalogBinding7Base
@[expose] public section
namespace SparseMonotiles.CompactCatalogBinding7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows12_checked : ∀ i : Fin 24, RowSame ⟨384 + i.val, by omega⟩ := by
  decide +kernel

#print axioms rows12_checked
end SparseMonotiles.CompactCatalogBinding7
