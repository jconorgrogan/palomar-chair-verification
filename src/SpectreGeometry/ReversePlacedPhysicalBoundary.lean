module

public import SpectreClusters.ReverseClusterBoundaryGlueData
public import SpectreGeometry.ReversePhysicalClusterInverseBoundary
public import SpectreGeometry.ReversePlacedPhysicalInverseCharts
public import SpectreGeometry.ReversePhysicalVertexParity
public import SpectreGeometry.ReversePhysicalCornerIntegration
public import SpectreGeometry.ReversePolygonalPathAffine

@[expose] public section


namespace SpectreGeometry.ReversePhysicalClusterCharts
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence Deformation ReverseExistence
open ReversePhysicalCluster ReverseClusterTriangulation SpectreFinite.HexSearch

/-- Affine inverse of an actual raw axial placement. -/
def rawUnplace (r : Fin 6) (a : RealPoint) : RealPoint →ᵃ[ℝ] RealPoint :=
  gridMotion (inverseTurn r) (-gridRotation (inverseTurn r) a)

@[simp] theorem rawUnplace_motion (r : Fin 6) (a p : RealPoint) :
    rawUnplace r a (a+gridRotation r p) = p := by
  change -(gridRotationLinear (inverseTurn r) a) +
    (gridRotationLinear (inverseTurn r)) (a+gridRotation r p) = p
  rw [map_add]
  have hc : gridRotation (inverseTurn r) (gridRotation r p) = p := by
    simpa only [inverseTurn_involutive] using gridRotation_inverse_cancel (inverseTurn r) p
  change -gridRotation (inverseTurn r) a +
    (gridRotation (inverseTurn r) a + gridRotation (inverseTurn r) (gridRotation r p)) = p
  rw [hc]
  abel

theorem rawUnplace_eq_symm (r : Fin 6) (a p : RealPoint) :
    rawUnplace r a p = (axialMotionHomeomorph r a).symm p := by
  obtain ⟨q,rfl⟩ := (axialMotionHomeomorph r a).surjective p
  rw [Homeomorph.symm_apply_apply,axialMotionHomeomorph_apply,rawUnplace_motion]

/-- The output placements use the proper physical rotation associated to the
raw axial turn and an independently integrated physical anchor. -/
def physicalMotion (r : Fin 6) (b : RealPoint) : RealPoint →ᵃ[ℝ] RealPoint :=
  (AffineEquiv.constVAdd ℝ RealPoint b).toAffineMap.comp
    (rotationLinearMap (physicalRootTurn r)).toAffineMap

@[simp] theorem physicalMotion_apply (r : Fin 6) (b p : RealPoint) :
    physicalMotion r b p = b+SpectreGeometry.rotate (physicalRootTurn r) p := rfl

def placedRawCoordinateInverse (big : Bool) (r : Fin 6) (a b p : RealPoint) : RealPoint :=
  physicalMotion r b (euclideanCoordinates.symm
    (rawClusterInverseMap big (rawUnplace r a p)))

theorem physical_state_path_real (k : Fin 9) (r d : Fin 6) :
    physicalPathReal (k,r) d =
      ((physicalPath4 k (sideTurn r d)).map quarterPoint).map
        (SpectreGeometry.rotate (physicalRootTurn r)) := by
  simp only [physicalPathReal,physicalStatePath4,physicalPath4,List.map_map]
  apply List.map_congr_left
  intro p hp
  exact physicalRotate4_vertexImage4_eval r (k.val != 0) p

/-- The entire directed raw boundary path is mapped to the physical P boundary
path with the same uniform parameter, including all subdivision endpoints. -/
theorem placedRawCoordinateInverse_boundary
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (k : Fin 9) (r d : Fin 6) (a b : RealPoint) (t : ℝ) (p : RealPoint)
    (hp : PathParameter ((statePath (k,r) d).map (fun q => a+integerPoint q)) t p) :
    PathParameter ((physicalPathReal (k,r) d).map (fun q => b+q)) t
      (placedRawCoordinateInverse (k.val != 0) r a b p) := by
  have hunplaced := hp.affineMap (rawUnplace r a)
  have hlist : ((statePath (k,r) d).map (fun q => a+integerPoint q)).map
      (rawUnplace r a) = ((markedPaths k).getD (sideTurn r d).val []).map integerPoint := by
    simp only [statePath,List.map_map]
    apply List.map_congr_left
    intro q hq
    simp only [Function.comp_apply,integerPoint_rotate,rawUnplace_motion]
  rw [hlist] at hunplaced
  have hraw := rawClusterInverseMap_markedBoundary hbinding hfaces k (sideTurn r d)
    t (rawUnplace r a p) hunplaced
  have hphysical := hraw.affineMap (physicalMotion r b)
  change PathParameter _ t (placedRawCoordinateInverse (k.val != 0) r a b p) at hphysical
  have htarget : ((physicalPath4 k (sideTurn r d)).map quarterPoint).map
      (physicalMotion r b) = (physicalPathReal (k,r) d).map (fun q => b+q) := by
    rw [physical_state_path_real]
    simp only [List.map_map,Function.comp_def,physicalMotion_apply]
  rwa [htarget] at hphysical

/-- The raw-coordinate description and the Euclidean residual-chart description
are exactly the same actual placed cluster inverse map. -/
theorem placedRawCoordinateInverse_frame
    (big : Bool) (r : Fin 6) (a b p : RealPoint) :
    euclideanCoordinates (placedRawCoordinateInverse big r a b p) =
      placedClusterInverse big r a b (rawEuclideanFrame p) := by
  obtain ⟨q,rfl⟩ := (axialMotionHomeomorph r a).surjective p
  have hframe : rawEuclideanFrame (axialMotionHomeomorph r a q) =
      rawEuclideanFrame a + physicalRotation r (rawEuclideanFrame q) := by
    change coordinateLinearEquiv (rawFrame (a+gridRotation r q)) =
      coordinateLinearEquiv (rawFrame a) + physicalRotation r (euclideanCoordinates (rawFrame q))
    rw [rawFrame.map_add,rawFrame_gridRotation,coordinateLinearEquiv.map_add,
      physicalRotation_coordinates]
    rfl
  rw [hframe]
  simp only [placedClusterInverse,add_sub_cancel_left,LinearIsometryEquiv.symm_apply_apply,
    Homeomorph.symm_apply_apply,placedRawCoordinateInverse,axialMotionHomeomorph_apply,
    rawUnplace_motion,physicalMotion_apply]
  change coordinateLinearEquiv (b+SpectreGeometry.rotate (physicalRootTurn r)
    (euclideanCoordinates.symm (rawClusterInverseMap big q))) = _
  rw [map_add]
  congr 1

end
end SpectreGeometry.ReversePhysicalClusterCharts
