module

public import SpectreGeometry.ReversePlacedClusterCharts
public import SpectreGeometry.ReverseMarkedBoundaryPathLaw
public import SpectreClusters.ReverseClusterBoundaryGlueData

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite.HexSearch
open ReverseClusterTriangulation

private theorem turn_side_inverse : ∀ r d : Fin 6, rotateTurn r (sideTurn r d) = d := by decide
private theorem turn_side_next : ∀ r d : Fin 6,
    rotateTurn r (sideTurn r d+1) = d+1 := by decide

theorem sourceSide_motion (r : Fin 6) (c : ℤ×ℤ) (d : Fin 6) (t : ℝ) :
    axialMotionHomeomorph r (integerPoint c)
      (AffineMap.lineMap (sourceHexCorner (sideTurn r d))
        (sourceHexCorner (sideTurn r d+1)) t) =
      AffineMap.lineMap (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1)) t := by
  change gridMotion r (integerPoint c) (AffineMap.lineMap _ _ t) = _
  rw [AffineMap.apply_lineMap]
  simp only [gridMotion_apply,gridRotation_sourceHexCorner,turn_side_inverse,turn_side_next]
  rfl

/-- Every placed marked closed-side chart follows the full actual directed
marked path with its uniform source parameter. -/
theorem placedClusterChart_pathParameter (k : Fin 9)
    (h : sourceHexCarrier (0,0) ≃ₜ rawClusterBody (clusterOfMark k))
    (hboundary : MarkedBoundarySubintervalLaw k (fun x => (h x).val))
    (r : Fin 6) (c : ℤ×ℤ) (a : RealPoint) (d : Fin 6)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : sourceHexCarrier c)
    (hx : x.val = AffineMap.lineMap (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1)) t) :
    PathParameter ((statePath (k,r) d).map (fun p => a+integerPoint p)) t
      (placedClusterChart h r c a x).val := by
  let q := (sourceHexMotionHomeomorph r c).symm x
  have hq : q.val = AffineMap.lineMap (sourceHexCorner (sideTurn r d))
      (sourceHexCorner (sideTurn r d+1)) t := by
    apply (axialMotionHomeomorph r (integerPoint c)).injective
    have he := congrArg Subtype.val ((sourceHexMotionHomeomorph r c).apply_symm_apply x)
    change axialMotionHomeomorph r (integerPoint c) q.val = x.val at he
    rw [he,sourceSide_motion]
    exact hx
  have hp := markedBoundary_pathParameter k (fun y => (h y).val) hboundary
    (sideTurn r d) t ht q hq
  have hm := hp.affineMap (gridMotion r a)
  change PathParameter _ t (a+gridRotation r (h q).val)
  have he : ((((markedPaths k).getD (sideTurn r d).val []).map integerPoint).map
      (gridMotion r a)) = (statePath (k,r) d).map (fun p => a+integerPoint p) := by
    simp only [statePath,List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply,gridMotion_apply,integerPoint_rotate]
  rw [he] at hm
  exact hm

end
end SpectreGeometry.ReverseExistence
