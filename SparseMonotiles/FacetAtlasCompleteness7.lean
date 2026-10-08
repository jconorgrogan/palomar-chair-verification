module

public import Mathlib.Tactic.FinCases
public import SparseMonotiles.FacetAtlasCompleteness7Axis0
public import SparseMonotiles.FacetAtlasCompleteness7Axis1
public import SparseMonotiles.FacetAtlasCompleteness7Axis2
public import SparseMonotiles.FacetAtlasCompleteness7Axis3
public import SparseMonotiles.FacetAtlasCompleteness7Axis4
public import SparseMonotiles.FacetAtlasCompleteness7Axis5
public import SparseMonotiles.FacetAtlasCompleteness7Axis6

@[expose] public section
namespace SparseMonotiles
open Contact
theorem T7_indexed_facets_complete (f : Facet 7)
    (hc : IsChairCell f.cell) (he : ¬ IsChairCell f.neighbor) :
    ∃ i : Fin 896, IndexedData7.geometry.facet i = f := by
  apply IndexedGeometry.facet_complete_of_binary_lookup IndexedData7.geometry
    FacetAtlasCompleteness7.lookup _ f hc he
  intro b j positive
  fin_cases j
  · exact FacetAtlasCompleteness7.axis0_checked b positive
  · exact FacetAtlasCompleteness7.axis1_checked b positive
  · exact FacetAtlasCompleteness7.axis2_checked b positive
  · exact FacetAtlasCompleteness7.axis3_checked b positive
  · exact FacetAtlasCompleteness7.axis4_checked b positive
  · exact FacetAtlasCompleteness7.axis5_checked b positive
  · exact FacetAtlasCompleteness7.axis6_checked b positive
#print axioms T7_indexed_facets_complete
end SparseMonotiles
