module

public import SpectreGeometry.ReverseRawInverseChartReal
public import SpectreGeometry.ReversePhysicalClusterPathsData
public import SpectreGeometry.ReverseInverseTileFacesBinding

@[expose] public section


namespace SpectreGeometry.ReversePhysicalCluster
noncomputable section
open Set SpectreClusters Deformation

/-- The common reflected raw frame is a genuine invertible linear change of
coordinates. It is not asserted to be an isometry for the product norm. -/
def rawFrameEquiv : RealPoint ≃ₗ[ℝ] RealPoint :=
  LinearEquiv.ofInjectiveEndo rawFrame
    (ReverseInverseTile.gridEmbeddingLinear_injective.comp
      ReverseInverseTile.gridReflectionLinear_injective)

def rawFrameHomeomorph : RealPoint ≃ₜ RealPoint :=
  rawFrameEquiv.toAffineEquiv.toHomeomorphOfFiniteDimensional

@[simp] theorem rawFrameHomeomorph_apply (p : RealPoint) :
    rawFrameHomeomorph p = rawFrame p := rfl

/-- A raw axial turn becomes the corresponding proper physical rotation after
the one fixed frame reflection. -/
theorem rawFrame_gridRotation (r : Fin 6) (p : RealPoint) :
    rawFrame (gridRotation r p) = SpectreGeometry.rotate (physicalRootTurn r) (rawFrame p) := by
  have hs : Real.sqrt (3:ℝ)^2=3 := Real.sq_sqrt (by norm_num)
  fin_cases r <;> ext <;>
    norm_num [rawFrame,gridEmbeddingLinear,gridReflectionLinear,gridRotation,
      physicalRootTurn,SpectreGeometry.rotate,complexMulReal,realDirection,realize,
      SpectreGeometry.direction,directions,Quad3.eval]
  all_goals ring_nf
  all_goals simp only [hs]
  all_goals ring

/-- Proper physical rotations are linear isometries of the Euclidean Hilbert
plane used in the residual estimates. -/
def physicalRotationLinear (r : Fin 6) : EPlane →ₗ[ℝ] EPlane :=
  coordinateLinearEquiv.toLinearMap.comp
    ((rotationLinearMap (physicalRootTurn r)).comp coordinateLinearEquiv.symm.toLinearMap)

def physicalRotation (r : Fin 6) : EPlane ≃ₗᵢ[ℝ] EPlane where
  toLinearEquiv := {
    toEquiv := euclideanRotationEquiv (physicalRootTurn r)
    map_add' := (physicalRotationLinear r).map_add
    map_smul' := (physicalRotationLinear r).map_smul }
  norm_map' x := by
    change ‖euclideanRotationEquiv (physicalRootTurn r) x‖ = ‖x‖
    have h := euclideanRotation_dist (physicalRootTurn r) x 0
    have hz : euclideanRotationEquiv (physicalRootTurn r) (0:EPlane) = 0 :=
      (physicalRotationLinear r).map_zero
    simpa only [hz,dist_zero_right] using h

@[simp] theorem physicalRotation_coordinates (r : Fin 6) (p : RealPoint) :
    physicalRotation r (euclideanCoordinates p) =
      euclideanCoordinates (SpectreGeometry.rotate (physicalRootTurn r) p) := by
  change coordinateLinearEquiv (SpectreGeometry.rotate (physicalRootTurn r)
    (coordinateLinearEquiv.symm (coordinateLinearEquiv p))) = _
  rw [coordinateLinearEquiv.symm_apply_apply]
  rfl

end
end SpectreGeometry.ReversePhysicalCluster
