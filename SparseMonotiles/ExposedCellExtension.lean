module

public import SparseMonotiles.ExposedCellExtensionKey
public import SparseMonotiles.ExposedFacetLiteralKeys
public import SparseMonotiles.FacetAtlasCompleteness5
public import SparseMonotiles.FacetAtlasCompleteness7

@[expose] public section

/-! # Every exposed unit facet extends the registered physical component
Atlas completeness and an actual literal key on each facet discharge every
local geometric input. The occupied neighbor uses the exact signed cell action.
-/
namespace SparseMonotiles
open Set Canonical Contact

theorem T5_exposed_facet_has_registered_neighbor
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5) (A : tiles)
    (f : Facet 5) (hf : IsChairCell f.cell) (hexposed : ¬ IsChairCell f.neighbor) :
    ∃ B : tiles, B ≠ A ∧ ∃ p : Pose 5,
      (g B).trans (g A).symm=p.euclidean.toIsometryEquiv ∧
      IsChairCell (p.inverseCell f.neighbor) := by
  obtain ⟨i,hfi⟩ := T5_indexed_facets_complete f hf hexposed
  obtain ⟨root,hprofile,hroot⟩ := T5_indexed_facet_has_literal_key i
  have hcollar : root.CollarValid 19200 f := by
    rw [← hfi]
    exact (atlas5_checked i).2.1 root hprofile
  exact T5_key_on_facet_has_registered_neighbor ht g hg A f hf root hroot hcollar

#print axioms T5_exposed_facet_has_registered_neighbor

theorem T7_exposed_facet_has_registered_neighbor
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7) (A : tiles)
    (f : Facet 7) (hf : IsChairCell f.cell) (hexposed : ¬ IsChairCell f.neighbor) :
    ∃ B : tiles, B ≠ A ∧ ∃ p : Pose 7,
      (g B).trans (g A).symm=p.euclidean.toIsometryEquiv ∧
      IsChairCell (p.inverseCell f.neighbor) := by
  obtain ⟨i,hfi⟩ := T7_indexed_facets_complete f hf hexposed
  obtain ⟨root,hprofile,hroot⟩ := T7_indexed_facet_has_literal_key i
  have hcollar : root.CollarValid 188160 f := by
    rw [← hfi]
    exact (atlas7_checked i).2.1 root hprofile
  exact T7_key_on_facet_has_registered_neighbor ht g hg A f hf root hroot hcollar

#print axioms T7_exposed_facet_has_registered_neighbor

end SparseMonotiles
