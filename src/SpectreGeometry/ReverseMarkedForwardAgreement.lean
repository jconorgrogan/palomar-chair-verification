module

public import SpectreGeometry.ReverseMarkedCarrierAtlas
public import SpectreGeometry.ReversePlacedBoundaryParameters
public import SpectreGeometry.ReversePolygonalPathTransforms
public import SpectreClusters.ReverseClusterBoundaryGlue

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation

def realDevelopedPath (f : Position → State) (hf : GloballyLegal f)
    (c : Position) (d : Fin 6) : List RealPoint :=
  (developedPath f hf c d).map integerPoint

theorem realDevelopedPath_eq (f : Position → State) (hf : GloballyLegal f)
    (c : Position) (d : Fin 6) :
    realDevelopedPath f hf c d =
      (statePath (f c) d).map (fun p => markedAnchor f hf c+integerPoint p) := by
  simp only [realDevelopedPath,developedPath,List.map_map]
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply,integerPoint_add]
  rfl

theorem realDevelopedPath_glue (f : Position → State) (hf : GloballyLegal f)
    (c : Position) (d : Fin 6) :
    realDevelopedPath f hf c d =
      (realDevelopedPath f hf (sourceHexNeighbor c d) (opposite d)).reverse := by
  unfold realDevelopedPath
  rw [developedPath_glue,List.map_reverse]
  rfl

theorem sourceHexNeighbor_side_reverse (c : Position) (d : Fin 6) (t : ℝ) :
    AffineMap.lineMap (sourceHexCornerAt (sourceHexNeighbor c d) (opposite d))
      (sourceHexCornerAt (sourceHexNeighbor c d) (opposite d+1)) (1-t) =
      AffineMap.lineMap (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1)) t := by
  fin_cases d <;> ext <;>
    norm_num [sourceHexCornerAt,sourceHexNeighbor,sourceHexCorner,opposite,SpectreFinite.direction,
      AffineMap.lineMap_apply_module] <;> ring

variable (hlocal : ∀ k : Fin 9, sourceHexCarrier (0,0) ≃ₜ rawClusterBody (clusterOfMark k))
variable (hboundary : ∀ k, MarkedBoundarySubintervalLaw k (fun x => (hlocal k x).val))
variable (f : Position → State) (hf : GloballyLegal f)
include hboundary

theorem markedPlacedChart_pathParameter (c : Position) (d : Fin 6)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : sourceHexCarrier c)
    (hx : x.val = AffineMap.lineMap (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1)) t) :
    PathParameter (realDevelopedPath f hf c d) t (markedPlacedChart hlocal f hf c x).val := by
  rw [realDevelopedPath_eq]
  exact placedClusterChart_pathParameter (f c).1 (hlocal (f c).1) (hboundary (f c).1)
    (f c).2 c (markedAnchor f hf c) d t ht x hx

/-- The whole source-side overlap agrees, including all mesh subdivision
vertices and both triple-corner endpoints. -/
theorem marked_neighbor_agreement : MarkedNeighborAgreement hlocal f hf := by
  intro c d p hp hq
  have hi : p ∈ segment ℝ (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1)) := by
    rw [←sourceHex_neighbor_intersection_segment]
    exact ⟨hp,hq⟩
  rw [segment_eq_image_lineMap] at hi
  obtain ⟨t,ht,hpEq⟩ := hi
  have hA := markedPlacedChart_pathParameter hlocal hboundary f hf c d t ht ⟨p,hp⟩ hpEq.symm
  have ht' : 1-t ∈ Icc (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hpEq' : p = AffineMap.lineMap (sourceHexCornerAt (sourceHexNeighbor c d) (opposite d))
      (sourceHexCornerAt (sourceHexNeighbor c d) (opposite d+1)) (1-t) := by
    rw [sourceHexNeighbor_side_reverse]
    exact hpEq.symm
  have hB := markedPlacedChart_pathParameter hlocal hboundary f hf
    (sourceHexNeighbor c d) (opposite d) (1-t) ht' ⟨p,hq⟩ hpEq'
  have hr := hB.reverse
  rw [←realDevelopedPath_glue,show 1-(1-t)=t by ring] at hr
  exact hA.unique hr

end
end SpectreGeometry.ReverseExistence
