module

public import SpectreGeometry.ReverseMarkedForwardAgreement
public import SpectreGeometry.ReversePolygonalPathVertices
public import SpectreGeometry.ReverseLocalStarOccurrencesData

@[expose] public section


/-! Literal target mesh boundary vertices coincide across neighboring marked
clusters, with the exact reversed subdivision index. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation ReverseLocalStarOccurrences

theorem stateTargetBoundary_eq_statePath (a : State) (d : Fin 6) :
    (stateBoundaryIds a d).map (fun v =>
      gridRotation a.2 ((1/6:ℝ) • integerPoint (targetVertex a.1 v))) =
      (statePath a d).map integerPoint := by
  have h := congrArg (List.map (gridRotation a.2))
    (normalizedTargetBoundary_eq_markedPath a.1 (sideTurn a.2 d))
  simpa only [normalizedTargetBoundary,stateBoundaryIds,statePath,List.map_map,
    Function.comp_def,integerPoint_rotate] using h

theorem realDevelopedPath_eq_target_vertices (f : Position → State) (hf : GloballyLegal f)
    (c : Position) (d : Fin 6) :
    realDevelopedPath f hf c d =
      (stateBoundaryIds (f c) d).map (fun v => markedAnchor f hf c+
        gridRotation (f c).2 ((1/6:ℝ) • integerPoint (targetVertex (f c).1 v))) := by
  rw [realDevelopedPath_eq]
  have h := congrArg (List.map (fun p : RealPoint => markedAnchor f hf c+p))
    (stateTargetBoundary_eq_statePath (f c) d)
  simpa only [List.map_map,Function.comp_def] using h.symm

theorem realDevelopedPath_length (f : Position → State) (hf : GloballyLegal f)
    (c : Position) (d : Fin 6) :
    (realDevelopedPath f hf c d).length = (stateBoundaryIds (f c) d).length := by
  rw [realDevelopedPath_eq_target_vertices,List.length_map]

theorem stateBoundaryIds_neighbor_length (f : Position → State) (hf : GloballyLegal f)
    (c : Position) (d : Fin 6) :
    (stateBoundaryIds (f c) d).length =
      (stateBoundaryIds (f (sourceHexNeighbor c d)) (opposite d)).length := by
  rw [←realDevelopedPath_length f hf c d,realDevelopedPath_glue,List.length_reverse,
    realDevelopedPath_length]

theorem realDevelopedPath_vertex (f : Position → State) (hf : GloballyLegal f)
    (c : Position) (d : Fin 6) (j : Nat)
    (hj : j < (stateBoundaryIds (f c) d).length) :
    (realDevelopedPath f hf c d).getD j 0 =
      markedAnchor f hf c + gridRotation (f c).2 ((1/6:ℝ) • integerPoint
        (targetVertex (f c).1 ((stateBoundaryIds (f c) d).getD j 0))) := by
  rw [realDevelopedPath_eq_target_vertices]
  simp [List.getD_eq_getElem?_getD,hj]

/-- Exact center identification for the two cached local stars on every
matching side, including both endpoint indices. -/
theorem marked_boundary_vertex_glue (f : Position → State) (hf : GloballyLegal f)
    (c : Position) (d : Fin 6) (j : Nat)
    (hj : j < (stateBoundaryIds (f c) d).length) :
    markedAnchor f hf c + gridRotation (f c).2 ((1/6:ℝ) • integerPoint
      (targetVertex (f c).1 ((stateBoundaryIds (f c) d).getD j 0))) =
    markedAnchor f hf (sourceHexNeighbor c d) +
      gridRotation (f (sourceHexNeighbor c d)).2 ((1/6:ℝ) • integerPoint
        (targetVertex (f (sourceHexNeighbor c d)).1
          ((stateBoundaryIds (f (sourceHexNeighbor c d)) (opposite d)).getD
            ((stateBoundaryIds (f (sourceHexNeighbor c d)) (opposite d)).length-1-j) 0))) := by
  have hlen := stateBoundaryIds_neighbor_length f hf c d
  have hj' : j < (realDevelopedPath f hf (sourceHexNeighbor c d) (opposite d)).length := by
    rw [realDevelopedPath_length]
    omega
  have hrev : (realDevelopedPath f hf (sourceHexNeighbor c d) (opposite d)).reverse.getD j 0 =
      (realDevelopedPath f hf (sourceHexNeighbor c d) (opposite d)).getD
        ((realDevelopedPath f hf (sourceHexNeighbor c d) (opposite d)).length-1-j) 0 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_reverse hj']
  rw [←realDevelopedPath_vertex f hf c d j hj,realDevelopedPath_glue,hrev,
    realDevelopedPath_length,realDevelopedPath_vertex]
  omega

end
end SpectreGeometry.ReverseExistence
