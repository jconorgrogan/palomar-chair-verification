module

public import SpectreGeometry.ReversePhysicalClusterInverseMap
public import SpectreGeometry.ReverseRawPhysicalRotations
public import SpectreGeometry.ReverseIsometricInverseGluing
public import SpectreGeometry.ReversePlacedClusterCharts

@[expose] public section


namespace SpectreGeometry.ReversePhysicalClusterCharts
noncomputable section
open Set SpectreClusters Deformation ReverseExistence ReversePhysicalCluster
open ReverseClusterTriangulation
open scoped NNReal

def rawEuclideanFrame : RealPoint ≃ₜ EPlane := rawFrameHomeomorph.trans euclideanCoordinates

@[simp] theorem rawEuclideanFrame_apply (p : RealPoint) :
    rawEuclideanFrame p = euclideanCoordinates (rawFrame p) := rfl

def indexedEuclideanInverseChart (big : Bool) (z : Fin (chartFamily big).length) :
    EPlane ≃ₜ EPlane :=
  rawPieceInverseChart big (z.val/12) ⟨z.val%12,Nat.mod_lt _ (by decide)⟩

theorem indexedRawInverseAffine_frame (big : Bool) (z : Fin (chartFamily big).length)
    (p : RealPoint) :
    indexedRawInverseAffine big z p = indexedEuclideanInverseChart big z (rawEuclideanFrame p) :=
  rawClusterInverseAffine_apply big _ _ p

def placedRawTriangle (big : Bool) (z : Fin (chartFamily big).length)
    (r : Fin 6) (a : RealPoint) : Set EPlane :=
  (fun p : RealPoint => rawEuclideanFrame a + physicalRotation r (rawEuclideanFrame p)) ''
    integerHull ((chartFamily big).getD z.val default).vertices

def placedRawChartInverse (big : Bool) (z : Fin (chartFamily big).length)
    (r : Fin 6) (a b : RealPoint) (x : EPlane) : EPlane :=
  euclideanCoordinates b + physicalRotation r
    (indexedEuclideanInverseChart big z ((physicalRotation r).symm (x-rawEuclideanFrame a)))

def placedClusterInverse (big : Bool) (r : Fin 6) (a b : RealPoint) (x : EPlane) : EPlane :=
  euclideanCoordinates b + physicalRotation r
    (rawClusterInverseMap big
      (rawEuclideanFrame.symm ((physicalRotation r).symm (x-rawEuclideanFrame a))))

theorem placedRawChartInverse_residual_lipschitz
    (big : Bool) (z : Fin (chartFamily big).length) (r : Fin 6) (a b : RealPoint) :
    LipschitzWith (15/16 : ℝ≥0)
      (fun x => x-(31/32:ℝ) • placedRawChartInverse big z r a b x) :=
  inverse_residual_lipschitz_placed _ (inverseAffineChart_residual_lipschitz _ _ _ _)
    (physicalRotation r) (euclideanCoordinates b) (rawEuclideanFrame a)

/-- Choice of a raw-cluster chart is immaterial on every actual placed triangle. -/
theorem placedClusterInverse_on
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (big : Bool) (z : Fin (chartFamily big).length) (r : Fin 6) (a b : RealPoint)
    (x : EPlane) (hx : x ∈ placedRawTriangle big z r a) :
    placedClusterInverse big r a b x = placedRawChartInverse big z r a b x := by
  obtain ⟨q,hq,rfl⟩ := hx
  simp only [placedClusterInverse,placedRawChartInverse,_root_.add_sub_cancel_left,
    LinearIsometryEquiv.symm_apply_apply,Homeomorph.symm_apply_apply]
  rw [rawClusterInverseMap_on hbinding hfaces big z q hq,indexedRawInverseAffine_frame]

/-- The residual charts live on the exact common reflected physical images
of the actual rotated raw triangle carriers. -/
theorem placedRawTriangle_eq_frame_image
    (big : Bool) (z : Fin (chartFamily big).length) (r : Fin 6) (a : RealPoint) :
    placedRawTriangle big z r a = rawEuclideanFrame ''
      (axialMotionHomeomorph r a '' integerHull ((chartFamily big).getD z.val default).vertices) := by
  rw [Set.image_image]
  apply Set.image_congr
  intro q hq
  change euclideanCoordinates (rawFrame a) + physicalRotation r
    (euclideanCoordinates (rawFrame q)) = euclideanCoordinates (rawFrame (a+gridRotation r q))
  rw [physicalRotation_coordinates]
  change coordinateLinearEquiv (rawFrame a) +
    coordinateLinearEquiv (SpectreGeometry.rotate (physicalRootTurn r) (rawFrame q)) =
      coordinateLinearEquiv (rawFrame (a+gridRotation r q))
  rw [rawFrame.map_add,rawFrame_gridRotation,coordinateLinearEquiv.map_add]

end
end SpectreGeometry.ReversePhysicalClusterCharts
