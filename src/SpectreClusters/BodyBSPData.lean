module

public import SpectreGeometry.HalfplaneCertificateData
public import SpectreGeometry.DeformationTriangulationData
public import SpectreClusters.DeformedLiteralBinding
public import SpectreClusters.BoundaryChains

@[expose] public section

namespace SpectreClusters.BodyBSP
open SpectreGeometry.HalfplaneCertificate
set_option maxRecDepth 100000
def unitFacet : Constraint := (0,0,1)
def targetVertexLists : HTKind → List (List Point)
  | .hat => [[(3,0),(3,-3),(4,-2)],[(2,0),(3,-3),(3,0)],[(3,-3),(4,-5),(4,-4)],[(4,-5),(1,-2),(2,-4)],[(3,-3),(1,-2),(4,-5)],[(2,0),(1,-2),(3,-3)],[(1,-2),(-1,-1),(0,-2)],[(-1,-1),(-2,1),(-2,0)],[(-1,-1),(0,0),(-2,1)],[(1,-2),(0,0),(-1,-1)],[(2,0),(0,0),(1,-2)],[(1,1),(0,0),(2,0)]]
  | .turtle => [[(1,1),(2,-1),(2,0)],[(0,0),(2,-1),(1,1)],[(2,-1),(5,-4),(4,-2)],[(5,-4),(3,-3),(4,-4)],[(2,-1),(3,-3),(5,-4)],[(0,0),(3,-3),(2,-1)],[(3,-3),(0,-3),(2,-4)],[(0,-3),(-3,0),(-2,-2)],[(0,-3),(-2,0),(-3,0)],[(3,-3),(-2,0),(0,-3)],[(0,0),(-2,0),(3,-3)],[(-2,1),(-2,0),(0,0)]]
def kiteVertexLists : HTKind → List (List Point)
  | .hat => [[(0,0),(2,-1),(2,0),(1,1)],[(0,0),(-2,1),(-2,0),(-1,-1)],[(0,0),(-1,-1),(0,-2),(1,-2)],[(0,0),(1,-2),(2,-2),(2,-1)],[(2,-4),(4,-5),(4,-4),(3,-3)],[(2,-4),(3,-3),(2,-2),(1,-2)],[(4,-2),(3,0),(2,0),(2,-1)],[(4,-2),(2,-1),(2,-2),(3,-3)]]
  | .turtle => [[(-2,-2),(0,-3),(0,-2),(-1,-1)],[(-2,-2),(-1,-1),(-2,0),(-3,0)],[(0,0),(2,-1),(2,0),(1,1)],[(0,0),(-2,1),(-2,0),(-1,-1)],[(0,0),(-1,-1),(0,-2),(1,-2)],[(0,0),(1,-2),(2,-2),(2,-1)],[(2,-4),(3,-3),(2,-2),(1,-2)],[(2,-4),(1,-2),(0,-2),(0,-3)],[(4,-2),(2,-1),(2,-2),(3,-3)],[(4,-2),(3,-3),(4,-4),(5,-4)]]
def targetFacets : HTKind → List (List Constraint)
  | .hat => [[(1,0,-3),(-1,1,6),(-2,-1,6)],[(3,1,-6),(-1,0,3),(0,-1,0)],[(2,1,-3),(-1,0,4),(-1,-1,0)],[(-1,-1,-1),(2,1,0),(1,2,6)],[(-1,-2,-3),(1,1,1),(-2,-1,3)],[(2,-1,-4),(1,2,3),(-3,-1,6)],[(-1,-2,-3),(1,1,2),(0,1,2)],[(-2,-1,-3),(1,0,2),(1,1,2)],[(-1,1,0),(-1,-2,0),(2,1,3)],[(-2,-1,0),(1,-1,0),(1,2,3)],[(0,-1,0),(2,1,0),(-2,1,4)],[(1,-1,0),(0,1,0),(-1,-1,2)]]
  | .turtle => [[(2,1,-3),(-1,0,2),(-1,-1,2)],[(1,2,0),(-2,-1,3),(1,-1,0)],[(1,1,-1),(-2,-1,6),(-1,-2,0)],[(-1,-2,-3),(1,1,0),(0,1,4)],[(2,1,-3),(1,2,3),(-1,-1,1)],[(1,1,0),(-2,-1,3),(-1,-2,0)],[(0,-1,-3),(1,2,6),(-1,1,6)],[(-1,-1,-3),(2,1,6),(1,2,6)],[(-3,-2,-6),(0,-1,0),(1,1,3)],[(-3,-5,-6),(3,2,6),(0,1,3)],[(0,-1,0),(3,5,6),(-1,-1,0)],[(1,0,2),(0,1,0),(-1,-2,0)]]
def kiteFacets : HTKind → List (List Constraint)
  | .hat => [[(1,2,0),(-1,0,2),(-1,-1,2),(1,-1,0)],[(-1,-2,0),(1,0,2),(1,1,2),(-1,1,0)],[(1,-1,0),(1,1,2),(0,1,2),(-2,-1,0)],[(2,1,0),(0,1,2),(-1,0,2),(-1,-2,0)],[(1,2,6),(-1,0,4),(-1,-1,0),(1,-1,-6)],[(-1,1,6),(-1,-1,0),(0,-1,-2),(2,1,0)],[(-2,-1,6),(0,-1,0),(1,0,-2),(1,2,0)],[(-1,-2,0),(1,0,-2),(1,1,0),(-1,1,6)]]
  | .turtle => [[(1,2,6),(-1,0,0),(-1,-1,-2),(1,-1,0)],[(-1,1,0),(-1,-1,-2),(0,-1,0),(2,1,6)],[(1,2,0),(-1,0,2),(-1,-1,2),(1,-1,0)],[(-1,-2,0),(1,0,2),(1,1,2),(-1,1,0)],[(1,-1,0),(1,1,2),(0,1,2),(-2,-1,0)],[(2,1,0),(0,1,2),(-1,0,2),(-1,-2,0)],[(-1,1,6),(-1,-1,0),(0,-1,-2),(2,1,0)],[(-2,-1,0),(0,-1,-2),(1,0,0),(1,2,6)],[(-1,-2,0),(1,0,-2),(1,1,0),(-1,1,6)],[(1,-1,-6),(1,1,0),(0,1,4),(-2,-1,6)]]
def targetFacetScales : HTKind → List (List Nat)
  | .hat => [[3,1,1],[1,3,1],[1,1,1],[3,1,1],[1,3,1],[1,1,1],[1,1,1],[1,1,1],[1,1,1],[1,1,1],[2,1,1],[1,2,1]]
  | .turtle => [[1,1,1],[1,1,1],[3,1,1],[1,1,1],[1,1,3],[3,1,1],[3,1,1],[3,1,1],[1,1,3],[1,1,3],[2,1,3],[1,2,1]]
def kiteFacetScales : HTKind → List (List Nat)
  | .hat => [[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,1,1]]
  | .turtle => [[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,1,1]]
def baseFrame : HTKind → Fin 12 | .hat => 1 | .turtle => 0
def canonicalVertex (kind : HTKind) (i : Fin 14) : Point :=
  DeformedLiteralBinding.literalVertex kind
    (DeformedLiteralBinding.literalIndex (baseFrame kind) i)
def canonicalTriangle (kind : HTKind) (i : Fin 12) : List Point :=
  [canonicalVertex kind (SpectreGeometry.Deformation.triangleIndex i 0),
   canonicalVertex kind (SpectreGeometry.Deformation.triangleIndex i 2),
   canonicalVertex kind (SpectreGeometry.Deformation.triangleIndex i 1)]
def edgeFacet (a b : Point) : Constraint :=
  (-(b.2-a.2),b.1-a.1,(b.2-a.2)*a.1-(b.1-a.1)*a.2)
def polygonFacets (vs : List Point) : List Constraint :=
  (cycleEdges vs).map (fun e => edgeFacet e.1 e.2)
def facetBindingB (vs : List Point) (fs : List Constraint) (scales : List Nat) : Bool :=
  (fs.length == scales.length) && scales.all (fun n => 0 < n) &&
    (List.zipWith scaleConstraint scales fs == polygonFacets vs)
theorem kite_vertices_bound (kind : HTKind) :
    kiteVertexLists kind = (htCells kind).map cellVertices := by cases kind <;> rfl
theorem target_vertices_bound (kind : HTKind) :
    targetVertexLists kind = (List.finRange 12).map (canonicalTriangle kind) := by cases kind <;> rfl
theorem target_facets_bound : ∀ kind : HTKind, ∀ i : Fin 12,
    facetBindingB ((targetVertexLists kind).getD i.val [])
      ((targetFacets kind).getD i.val []) ((targetFacetScales kind).getD i.val []) = true := by intro kind; cases kind <;> decide
theorem kite_facets_bound : ∀ kind : HTKind, ∀ i : Fin (htCells kind).length,
    facetBindingB ((kiteVertexLists kind).getD i.val [])
      ((kiteFacets kind).getD i.val []) ((kiteFacetScales kind).getD i.val []) = true := by intro kind; cases kind <;> decide
theorem target_facets_length (kind : HTKind) : (targetFacets kind).length = 12 := by cases kind <;> rfl
theorem kite_facets_length (kind : HTKind) : (kiteFacets kind).length = (htCells kind).length := by cases kind <;> rfl
def edgeValue (line : Constraint) (p : Point) : Int :=
  line.1*p.1 + line.2.1*p.2 + line.2.2

def polygonPositiveB (vs : List Point) : Bool :=
  (List.range vs.length).all fun i =>
    0 < edgeValue (edgeFacet (vs.getD i (0,0))
      (vs.getD ((i+1)%vs.length) (0,0))) (vs.getD ((i+2)%vs.length) (0,0))

theorem target_triangles_positive : ∀ kind : HTKind, ∀ i : Fin 12,
    polygonPositiveB ((targetVertexLists kind).getD i.val []) = true := by
  intro kind; cases kind <;> decide

theorem kite_convex_positive : ∀ kind : HTKind, ∀ i : Fin (htCells kind).length,
    polygonPositiveB ((kiteVertexLists kind).getD i.val []) = true := by
  intro kind; cases kind <;> decide

end SpectreClusters.BodyBSP
