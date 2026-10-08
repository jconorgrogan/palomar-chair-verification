module
public import CatalogInverseBase
@[expose] public section
namespace SparseMonotiles.ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem inverse_rows_6 : ∀ i : Fin 32, CatalogInverseRow ⟨192 + i.val, by omega⟩ := by
  decide +kernel

#print axioms inverse_rows_6
end SparseMonotiles.ContactInverseReuse
