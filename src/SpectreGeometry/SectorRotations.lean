module

public import SpectreGeometry.CyclicFrameRegistration
public import SpectreGeometry.CornerGermData

@[expose] public section


/-! Actual affine transport of the twelve open-sector sample rays between
the derived relative frames. -/
namespace SpectreGeometry
noncomputable section

theorem direction_add_zero (a : Fin 12) : directionAdd a 0 = a := by
  apply Fin.ext
  simp [directionAdd]
theorem direction_zero_add (a : Fin 12) : directionAdd 0 a = a := by
  apply Fin.ext
  simp [directionAdd]
theorem direction_add_comm (a b : Fin 12) : directionAdd a b = directionAdd b a := by
  apply Fin.ext
  simp only [directionAdd,Nat.add_comm]

theorem realize_add (x y : ExactPoint) : realize (ExactPoint.add x y) = realize x+realize y := by
  apply Prod.ext <;> simp [realize,ExactPoint.add,Quad3.eval_add,add_div]

theorem sector_real_vector (d : Fin 12) : realize (sectorVector d) =
    realDirection d+realDirection (directionAdd d 1) := realize_add _ _

theorem rotate_add_vector (k : Fin 12) (x y : RealPoint) :
    rotate k (x+y) = rotate k x+rotate k y := by
  apply Prod.ext <;> simp only [rotate,complexMulReal,Prod.fst_add,Prod.snd_add] <;> ring

theorem rotate_sector_vector (k d : Fin 12) :
    rotate k (realize (sectorVector d)) = realize (sectorVector (directionAdd k d)) := by
  rw [sector_real_vector,rotate_add_vector]
  change complexMulReal (realDirection k) (realDirection d)+
    complexMulReal (realDirection k) (realDirection (directionAdd d 1)) = _
  rw [realDirection_multiply,realDirection_multiply,sector_real_vector,direction_add_assoc]

theorem inverse_linear_part (f : EPlane ≃ᵢ EPlane) (v : EPlane) :
    f.symm.toRealLinearIsometryEquiv (f.toRealLinearIsometryEquiv v) = v := by
  rw [IsometryEquiv.toRealLinearIsometryEquiv_apply f,map_sub,
    IsometryEquiv.toRealLinearIsometryEquiv_apply,IsometryEquiv.toRealLinearIsometryEquiv_apply,
    f.symm_apply_apply,f.symm_apply_apply]
  abel

theorem pullback_linear_part (f : EPlane ≃ᵢ EPlane) (q : RealPoint) :
    displacementPullback f (f.toRealLinearIsometryEquiv (euclideanCoordinates q)) = q := by
  change coordinateLinearEquiv.symm (f.symm.toRealLinearIsometryEquiv
    (f.toRealLinearIsometryEquiv (coordinateLinearEquiv q))) = q
  rw [inverse_linear_part,coordinateLinearEquiv.symm_apply_apply]

def framedSectorVector (f : EPlane ≃ᵢ EPlane) (d : Fin 12) : EPlane :=
  f.toRealLinearIsometryEquiv (euclideanCoordinates (realize (sectorVector d)))

theorem relative_pullback_sector (root f : EPlane ≃ᵢ EPlane) (k : Fin 12)
    (hframe : ∀ q : RealPoint, coordinateAction f q = coordinateAction root (rotate k q))
    (d : Fin 12) : displacementPullback f (framedSectorVector root d) =
      realize (sectorVector (directionAdd (directionInverse k) d)) := by
  let q := realize (sectorVector (directionAdd (directionInverse k) d))
  have hrot : rotate k q = realize (sectorVector d) := by
    dsimp only [q]
    rw [rotate_sector_vector,←direction_add_assoc,direction_inverse_right,direction_zero_add]
  have hh := hframe q
  rw [hrot] at hh
  have hh' := congrArg coordinateLinearEquiv hh
  change coordinateLinearEquiv (coordinateLinearEquiv.symm
    (f.toRealLinearIsometryEquiv (euclideanCoordinates q))) =
    coordinateLinearEquiv (coordinateLinearEquiv.symm (framedSectorVector root d)) at hh'
  simp only [coordinateLinearEquiv.apply_symm_apply] at hh'
  rw [←hh',pullback_linear_part]

def framedRay (root : EPlane ≃ᵢ EPlane) (x : EPlane) (d : Fin 12) (t : ℝ) : EPlane :=
  x+t • framedSectorVector root d

theorem preimage_add_displacement (f : EPlane ≃ᵢ EPlane) (x v : EPlane) (t : ℝ) :
    euclideanCoordinates.symm (f.symm (x+t • v)) =
      euclideanCoordinates.symm (f.symm x)+t • displacementPullback f v := by
  have h := displacementPullback_sub f x (x+t • v)
  simp only [add_sub_cancel_left,map_smul] at h
  have he := eq_add_of_sub_eq h.symm
  simpa only [add_comm] using he

theorem relative_preimage_ray (root f : EPlane ≃ᵢ EPlane) (k : Fin 12)
    (hframe : ∀ q : RealPoint, coordinateAction f q = coordinateAction root (rotate k q))
    (x : EPlane) (d : Fin 12) (t : ℝ) :
    euclideanCoordinates.symm (f.symm (framedRay root x d t)) =
      euclideanCoordinates.symm (f.symm x)+t •
        realize (sectorVector (directionAdd (directionInverse k) d)) := by
  rw [framedRay,preimage_add_displacement,relative_pullback_sector root f k hframe]

end
end SpectreGeometry
