module
public import CatalogInverseBase
@[expose] public section
namespace SparseMonotiles.ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem inverse_rows_7 : ∀ i : Fin 32, CatalogInverseRow ⟨224 + i.val, by omega⟩ := by
  decide +kernel

#print axioms inverse_rows_7
end SparseMonotiles.ContactInverseReuse
