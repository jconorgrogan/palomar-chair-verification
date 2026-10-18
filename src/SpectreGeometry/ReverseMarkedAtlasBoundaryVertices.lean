module

public import SpectreGeometry.ReverseMarkedPathVertexCenters
public import SpectreGeometry.ReversePolygonalPathCarrier
public import SpectreGeometry.ReverseMarkedBoundaryIndexBounds
public import SpectreGeometry.ReverseLocalStarPlacedNeighborhood

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation ReverseLocalStarOccurrences ReverseFinitePL

variable (hlocal : ∀ k : Fin 9, sourceHexCarrier (0,0) ≃ₜ rawClusterBody (clusterOfMark k))
variable (hboundary : ∀ k, MarkedBoundarySubintervalLaw k (fun x => (hlocal k x).val))
variable (f : Position → State) (hf : GloballyLegal f)

include hboundary in
/-- Every placed chart sends a source boundary subdivision vertex to its
literal target vertex, with the same uniform full-side parameter. -/
theorem markedPlacedChart_boundary_vertex (c : Position) (d : Fin 6) (j : Nat)
    (hj : j < (stateBoundaryIds (f c) d).length) (x : sourceHexCarrier c)
    (hx : x.val = AffineMap.lineMap (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1))
      ((j:ℝ)/((stateBoundaryIds (f c) d).length-1:Nat))) :
    (markedPlacedChart hlocal f hf c x).val =
      markedAnchor f hf c+gridRotation (f c).2 ((1/6:ℝ) • integerPoint
        (targetVertex (f c).1 ((stateBoundaryIds (f c) d).getD j 0))) := by
  have hn : 2 ≤ (realDevelopedPath f hf c d).length := by
    rw [realDevelopedPath_length]
    exact (all_boundary_linear_checks (f c).1 (sideTurn (f c).2 d)).1
  have hp := pathParameter_vertex (realDevelopedPath f hf c d) hn j
    (by rwa [realDevelopedPath_length])
  rw [realDevelopedPath_length] at hp
  have hc := markedPlacedChart_pathParameter hlocal hboundary f hf c d _
    hp.parameter_mem x hx
  have he := hc.unique hp
  rw [realDevelopedPath_vertex f hf c d j hj] at he
  exact he

include hf in
/-- The source-side subdivision parameter is in its full closed side. -/
theorem boundary_vertex_parameter_mem (c : Position) (d : Fin 6) (j : Nat)
    (hj : j < (stateBoundaryIds (f c) d).length) :
    ((j:ℝ)/((stateBoundaryIds (f c) d).length-1:Nat)) ∈ Icc (0:ℝ) 1 := by
  have hn : 2 ≤ (realDevelopedPath f hf c d).length := by
    rw [realDevelopedPath_length]
    exact (all_boundary_linear_checks (f c).1 (sideTurn (f c).2 d)).1
  have hp := pathParameter_vertex (realDevelopedPath f hf c d) hn j
    (by rwa [realDevelopedPath_length])
  rw [realDevelopedPath_length] at hp
  exact hp.parameter_mem

include hboundary in
/-- At each noncorner marked subdivision vertex, the actual atlas image is
interior to the union of its two neighboring target carriers. -/
theorem marked_side_vertex_interior
    (hraw : ∀ big v, RawStarBinding big v) (hrows : IncidentRowsCorrect)
    (hcert : ∀ i : Fin 217, SideGeometryCertificate i.val)
    (hbind : ∀ k d, SideGeometryBinding k d)
    (c : Position) (d : Fin 6) (j : Fin 12)
    (hj : 0<j.val) (hj' : j.val+1<(stateBoundaryIds (f c) d).length)
    (x : sourceHexCarrier c)
    (hx : x.val = AffineMap.lineMap (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1))
      ((j.val:ℝ)/((stateBoundaryIds (f c) d).length-1:Nat))) :
    (markedPlacedChart hlocal f hf c x).val ∈
      interior (markedTargetCarrier f hf c ∪
        markedTargetCarrier f hf (sourceHexNeighbor c d)) := by
  have hja : j.val < (stateBoundaryIds (f c) d).length := by omega
  have hlen := stateBoundaryIds_neighbor_length f hf c d
  have hjb : (stateBoundaryIds (f (sourceHexNeighbor c d)) (opposite d)).length-1-j.val <
      (stateBoundaryIds (f (sourceHexNeighbor c d)) (opposite d)).length := by omega
  have hA := markedPlacedChart_boundary_vertex hlocal hboundary f hf c d j.val hja x hx
  have hB := marked_boundary_vertex_glue f hf c d j.val hja
  change _ ∈ interior (placedClusterCarrier (f c).2 (markedAnchor f hf c) _ ∪
    placedClusterCarrier (f (sourceHexNeighbor c d)).2
      (markedAnchor f hf (sourceHexNeighbor c d)) _)
  exact side_placed_origin_interior hraw hrows hcert hbind (f c)
    (f (sourceHexNeighbor c d)) d j (field_sideMatch f hf c d) hj hj'
    (markedAnchor f hf c) (markedAnchor f hf (sourceHexNeighbor c d)) _
    (boundary_vertex_index_bound (f c).1 (sideTurn (f c).2 d) j.val hja).2
    (boundary_vertex_index_bound (f (sourceHexNeighbor c d)).1
      (sideTurn (f (sourceHexNeighbor c d)).2 (opposite d)) _ hjb).2
    hA.symm (hB.symm.trans hA.symm)

/-- The two carriers above are precisely incident source-chart targets at
this point, so their ambient neighborhood is also one in the atlas target star. -/
theorem marked_side_vertex_targetStar_interior
    (hraw : ∀ big v, RawStarBinding big v) (hrows : IncidentRowsCorrect)
    (hcert : ∀ i : Fin 217, SideGeometryCertificate i.val)
    (hbind : ∀ k d, SideGeometryBinding k d)
    (c : Position) (d : Fin 6) (j : Fin 12)
    (hj : 0<j.val) (hj' : j.val+1<(stateBoundaryIds (f c) d).length)
    (x : sourceHexCarrier c)
    (hx : x.val = AffineMap.lineMap (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1))
      ((j.val:ℝ)/((stateBoundaryIds (f c) d).length-1:Nat))) :
    (markedCarrierAtlas hlocal f hf (marked_neighbor_agreement hlocal hboundary f hf)).map x.val ∈
      interior ((markedCarrierAtlas hlocal f hf
        (marked_neighbor_agreement hlocal hboundary f hf)).targetStar x.val) := by
  let A := markedCarrierAtlas hlocal f hf (marked_neighbor_agreement hlocal hboundary f hf)
  have hja : j.val < (stateBoundaryIds (f c) d).length := by omega
  have hneighbor : x.val ∈ sourceHexCarrier (sourceHexNeighbor c d) := by
    have hp : x.val ∈ sourceHexCarrier c ∩ sourceHexCarrier (sourceHexNeighbor c d) := by
      rw [sourceHex_neighbor_intersection_segment,hx]
      exact lineMap_mem_segment ℝ _ _ (boundary_vertex_parameter_mem f hf c d j.val hja)
    exact hp.2
  have hsub : markedTargetCarrier f hf c ∪ markedTargetCarrier f hf (sourceHexNeighbor c d) ⊆
      A.targetStar x.val := by
    rintro y (hy | hy)
    · exact mem_iUnion.mpr ⟨⟨c,x.property⟩,hy⟩
    · exact mem_iUnion.mpr ⟨⟨sourceHexNeighbor c d,hneighbor⟩,hy⟩
  have hi := marked_side_vertex_interior hlocal hboundary f hf hraw hrows hcert hbind
    c d j hj hj' x hx
  change A.map x.val ∈ interior (A.targetStar x.val)
  rw [A.map_on c x.val x.property]
  exact interior_mono hsub hi

end
end SpectreGeometry.ReverseExistence
