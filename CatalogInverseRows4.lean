module
public import CatalogInverseBase
@[expose] public section
namespace SparseMonotiles.ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem inverse_rows_4 : ∀ i : Fin 32, CatalogInverseRow ⟨128 + i.val, by omega⟩ := by
  decide +kernel

#print axioms inverse_rows_4
end SparseMonotiles.ContactInverseReuse
