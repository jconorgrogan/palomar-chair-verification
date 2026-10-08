module
public import CatalogInverseBase
@[expose] public section
namespace SparseMonotiles.ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem inverse_rows_8 : ∀ i : Fin 32, CatalogInverseRow ⟨256 + i.val, by omega⟩ := by
  decide +kernel

#print axioms inverse_rows_8
end SparseMonotiles.ContactInverseReuse
