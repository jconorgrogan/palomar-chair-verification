module

public import Mathlib.Tactic.FinCases
public import SparseMonotiles.FacetAtlasCompleteness5Axis0
public import SparseMonotiles.FacetAtlasCompleteness5Axis1
public import SparseMonotiles.FacetAtlasCompleteness5Axis2
public import SparseMonotiles.FacetAtlasCompleteness5Axis3
public import SparseMonotiles.FacetAtlasCompleteness5Axis4

@[expose] public section
namespace SparseMonotiles
open Contact
theorem T5_indexed_facets_complete (f : Facet 5)
    (hc : IsChairCell f.cell) (he : ¬ IsChairCell f.neighbor) :
    ∃ i : Fin 160, IndexedData5.geometry.facet i = f := by
  apply IndexedGeometry.facet_complete_of_binary_lookup IndexedData5.geometry
    FacetAtlasCompleteness5.lookup _ f hc he
  intro b j positive
  fin_cases j
  · exact FacetAtlasCompleteness5.axis0_checked b positive
  · exact FacetAtlasCompleteness5.axis1_checked b positive
  · exact FacetAtlasCompleteness5.axis2_checked b positive
  · exact FacetAtlasCompleteness5.axis3_checked b positive
  · exact FacetAtlasCompleteness5.axis4_checked b positive
#print axioms T5_indexed_facets_complete
end SparseMonotiles
