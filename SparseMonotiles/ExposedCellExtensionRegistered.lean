module

public import SparseMonotiles.ExposedCellExtension
public import SparseMonotiles.RegisteredGridExtension

@[expose] public section

/-! The exact input to global integer-grid component exhaustion is now derived
from the actual tiling, not supplied as a registration hypothesis. -/
namespace SparseMonotiles
open Set Contact

theorem T5_registered_exposed_extension
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, g A '' T5=(A : Set (Point 5))) : RegisteredExposedExtension g := by
  intro A f hf he
  obtain ⟨B,hBA,p,hp,hcell⟩ := T5_exposed_facet_has_registered_neighbor ht g
    (fun A => (hg A).symm) A f hf he
  exact ⟨B,p,hp,hcell⟩

theorem T7_registered_exposed_extension
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, g A '' T7=(A : Set (Point 7))) : RegisteredExposedExtension g := by
  intro A f hf he
  obtain ⟨B,hBA,p,hp,hcell⟩ := T7_exposed_facet_has_registered_neighbor ht g
    (fun A => (hg A).symm) A f hf he
  exact ⟨B,p,hp,hcell⟩

#print axioms T5_registered_exposed_extension
#print axioms T7_registered_exposed_extension
end SparseMonotiles
