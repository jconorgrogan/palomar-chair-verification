module

public import SpectreGeometry.PhysicalGridRealization
public import SpectreGeometry.ReversePhysicalClusterChartFacesData

@[expose] public section


namespace SpectreGeometry.ReversePhysicalCluster
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP SpectreClusters.DeformedLiteralBinding
open Deformation ReversePhysicalClusterCharts

/-- The physical vertex indexing is exactly the indexing of the already
BSP-certified canonical H/T triangulation. -/
theorem physicalIndex_eq_canonical (kind : HTKind) (e : Fin 14) :
    physicalIndex kind e = literalIndex (baseFrame kind) e := by
  cases kind <;> rfl

def rawPlacedTriangleVertices (p : HTPlacement) (i : Fin 12) : List SpectreClusters.Point :=
  [rawPlacedVertex p (physicalIndex p.kind (triangleIndex i 0)),
   rawPlacedVertex p (physicalIndex p.kind (triangleIndex i 2)),
   rawPlacedVertex p (physicalIndex p.kind (triangleIndex i 1))]

theorem rawPlacedTriangleVertices_eq_motion (p : HTPlacement) (i : Fin 12) :
    rawPlacedTriangleVertices p i = (canonicalTriangle p.kind i).map
      (fun q => SpectreClusters.add (lattice p.center) (SpectreClusters.rotate p.turn q)) := by
  simp only [rawPlacedTriangleVertices,canonicalTriangle,canonicalVertex,
    List.map_cons,List.map_nil,rawPlacedVertex,physicalIndex_eq_canonical,literalVertex]

/-- The twelve actual raw inverse-chart triangles cover the complete placed
H/T carrier, using the existing exact BSP carrier theorem. -/
theorem placementKiteBody_eq_raw_triangles (p : HTPlacement) :
    placementKiteBody p = ⋃ i : Fin 12, integerHull (rawPlacedTriangleVertices p i) := by
  rw [placementKiteBody_image_literal,←canonicalTargetBody_eq_literalKiteBody,
    canonicalTargetBody,image_iUnion]
  apply iUnion_congr
  intro i
  rw [targetVertexLists_get,rawPlacedTriangleVertices_eq_motion,integerHull_image_motion]

theorem rawChartVertices_eq_rawPlacedTriangleVertices (big : Bool) (n : Nat) (i : Fin 12) :
    rawChartVertices big n i =
      rawPlacedTriangleVertices ((pieces big).getD n ⟨.turtle,0,(0,0)⟩) i := by
  rfl

theorem raw_piece_covered_by_chart_triangles (big : Bool) (n : Nat) :
    placementKiteBody ((pieces big).getD n ⟨.turtle,0,(0,0)⟩) =
      ⋃ i : Fin 12, integerHull (rawChartVertices big n i) := by
  simp only [rawChartVertices_eq_rawPlacedTriangleVertices]
  exact placementKiteBody_eq_raw_triangles _

end
end SpectreGeometry.ReversePhysicalCluster
