module

public import SpectreGeometry.DeformationHomeomorphismCarrierPeriod

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set Deformation

theorem coordinateAction_euclideanRotation (k : Fin 12) (p : RealPoint) :
    coordinateAction (euclideanRotation k) p = SpectreGeometry.rotate k p := by
  have h (q : RealPoint) : euclideanCoordinates.symm
      (euclideanRotation k (euclideanCoordinates q)) = SpectreGeometry.rotate k q := by
    change coordinateLinearEquiv.symm (coordinateLinearEquiv
      (SpectreGeometry.rotate k (coordinateLinearEquiv.symm (coordinateLinearEquiv q)))) = _
    rw [coordinateLinearEquiv.symm_apply_apply,coordinateLinearEquiv.symm_apply_apply]
  rw [coordinateAction_apply,h]
  have hz : euclideanCoordinates.symm (euclideanRotation k (0:EPlane)) = 0 := by
    rw [show (0:EPlane)=euclideanCoordinates (0:RealPoint) from (coordinateLinearEquiv.map_zero).symm,h]
    exact (rotationLinearMap k).map_zero
  rw [hz,sub_zero]

/-- Every displayed C12 rotation is a direct Euclidean placement. -/
theorem euclideanRotation_direct (k : Fin 12) : DirectPlacement (euclideanRotation k) := by
  unfold DirectPlacement frameFirst frameSecond
  rw [coordinateAction_euclideanRotation,coordinateAction_euclideanRotation]
  have he : RealPoint.det (SpectreGeometry.rotate k (1,0))
      (SpectreGeometry.rotate k (0,1)) = 1 := by
    simpa [SpectreGeometry.rotate,complexMulReal,RealPoint.det] using rotation_determinant_one k
  rw [he]
  norm_num

/-- The final P carrier poses use proper rotations and translations only. -/
def properPPlacement (k : Fin 12) (a : RealPoint) : EPlane ≃ᵢ EPlane :=
  translatedPlacement (euclideanRotation k) (euclideanCoordinates a)

theorem properPPlacement_direct (k : Fin 12) (a : RealPoint) :
    DirectPlacement (properPPlacement k a) :=
  translatedPlacement_direct (euclideanRotation k) (euclideanRotation_direct k) _

@[simp] theorem properPPlacement_apply (k : Fin 12) (a p : RealPoint) :
    properPPlacement k a (euclideanCoordinates p) =
      euclideanCoordinates (a+SpectreGeometry.rotate k p) := by
  change coordinateLinearEquiv (SpectreGeometry.rotate k
    (coordinateLinearEquiv.symm (coordinateLinearEquiv p)))+coordinateLinearEquiv a = _
  rw [coordinateLinearEquiv.symm_apply_apply,←map_add,add_comm]
  rfl

end
end SpectreGeometry.ReverseExistence
