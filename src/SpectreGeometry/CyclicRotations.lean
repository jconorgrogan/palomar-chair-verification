module

public import SpectreGeometry.EuclideanCarrier
public import SpectreGeometry.RotationData

@[expose] public section


/-! The twelve explicit directions form genuine orientation-preserving
rotations of the Euclidean plane. This constructs an allowed finite group;
it does not assert that arbitrary physical tilings are already registered. -/
namespace SpectreGeometry
noncomputable section

def complexMulReal (x y : RealPoint) : RealPoint :=
  (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1)
def rotate (d : Fin 12) (x : RealPoint) : RealPoint := complexMulReal (realDirection d) x

theorem complexMulReal_assoc (x y z : RealPoint) :
    complexMulReal x (complexMulReal y z) = complexMulReal (complexMulReal x y) z := by
  apply Prod.ext <;> simp only [complexMulReal] <;> ring

theorem realDirection_multiply (a b : Fin 12) :
    complexMulReal (realDirection a) (realDirection b) = realDirection (directionAdd a b) := by
  have h := direction_multiply a b
  have h1 := congrArg (fun p : ExactPoint => Quad3.eval p.1) h
  have h2 := congrArg (fun p : ExactPoint => Quad3.eval p.2) h
  simp only [complexMulExact,ExactPoint.add,Quad3.eval_add,Quad3.eval_sub,Quad3.eval_mul] at h1 h2
  apply Prod.ext
  · simp only [complexMulReal,realDirection,realize]
    nlinarith [h1]
  · simp only [complexMulReal,realDirection,realize]
    nlinarith [h2]

theorem rotate_add (a b : Fin 12) (x : RealPoint) :
    rotate a (rotate b x) = rotate (directionAdd a b) x := by
  unfold rotate
  rw [complexMulReal_assoc,realDirection_multiply]

theorem rotate_zero (x : RealPoint) : rotate 0 x = x := by
  simp [rotate,complexMulReal,realDirection,realize,direction,directions,Quad3.eval]

theorem rotate_inverse_left (d : Fin 12) (x : RealPoint) : rotate (directionInverse d) (rotate d x) = x := by
  rw [rotate_add,direction_inverse_left,rotate_zero]

theorem rotate_inverse_right (d : Fin 12) (x : RealPoint) : rotate d (rotate (directionInverse d) x) = x := by
  rw [rotate_add,direction_inverse_right,rotate_zero]

theorem complexMulReal_dot_self (x y : RealPoint) :
    RealPoint.dot (complexMulReal x y) (complexMulReal x y) = RealPoint.dot x x * RealPoint.dot y y := by
  simp only [RealPoint.dot,complexMulReal]
  ring

theorem rotate_sub (d : Fin 12) (x y : RealPoint) :
    RealPoint.sub (rotate d x) (rotate d y) = rotate d (RealPoint.sub x y) := by
  apply Prod.ext <;> simp only [rotate,RealPoint.sub,complexMulReal] <;> ring

theorem rotate_distance_squared (d : Fin 12) (x y : RealPoint) :
    RealPoint.dot (RealPoint.sub (rotate d x) (rotate d y)) (RealPoint.sub (rotate d x) (rotate d y)) =
      RealPoint.dot (RealPoint.sub x y) (RealPoint.sub x y) := by
  rw [rotate_sub]
  unfold rotate
  rw [complexMulReal_dot_self,real_directions_unit_squared,one_mul]

def coordinateRotationEquiv (d : Fin 12) : RealPoint ≃ RealPoint where
  toFun := rotate d
  invFun := rotate (directionInverse d)
  left_inv := rotate_inverse_left d
  right_inv := rotate_inverse_right d

def euclideanRotationEquiv (d : Fin 12) : EuclideanSpace ℝ (Fin 2) ≃ EuclideanSpace ℝ (Fin 2) :=
  euclideanCoordinates.symm.toEquiv.trans ((coordinateRotationEquiv d).trans euclideanCoordinates.toEquiv)

theorem euclideanRotation_dist (d : Fin 12) (x y : EuclideanSpace ℝ (Fin 2)) :
    dist (euclideanRotationEquiv d x) (euclideanRotationEquiv d y) = dist x y := by
  have hs : dist (euclideanRotationEquiv d x) (euclideanRotationEquiv d y)^2 = dist x y^2 := by
    change dist (euclideanCoordinates (rotate d (euclideanCoordinates.symm x)))
      (euclideanCoordinates (rotate d (euclideanCoordinates.symm y)))^2 = _
    rw [euclideanCoordinates_dist_squared,rotate_distance_squared,
      ←euclideanCoordinates_dist_squared]
    simp
  have hl := dist_nonneg (x := euclideanRotationEquiv d x) (y := euclideanRotationEquiv d y)
  have hr := dist_nonneg (x := x) (y := y)
  nlinarith

def euclideanRotation (d : Fin 12) : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2) where
  toEquiv := euclideanRotationEquiv d
  isometry_toFun := Isometry.of_dist_eq (euclideanRotation_dist d)

/-- The determinant of the displayed coordinate rotation matrix is one. -/
theorem rotation_determinant_one (d : Fin 12) :
    (realDirection d).1*(realDirection d).1-(-(realDirection d).2)*(realDirection d).2 = 1 := by
  have h := real_directions_unit_squared d
  dsimp [RealPoint.dot] at h
  nlinarith

end
end SpectreGeometry
