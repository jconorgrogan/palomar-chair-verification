module

public import LiteralPlanar.QuinticRigidity
public import SpectreGeometry.DirectIsometryFrames

@[expose] public section


/-! Coordinate adapter from an unrestricted Euclidean plane isometry to the
orthogonal affine coefficients used by the quintic graph-rigidity theorem.
No restriction to a finite rotation group is imposed. -/
namespace LiteralPlanar.Quintic
noncomputable section
open SpectreGeometry

theorem frame_determinant_squared (f : EPlane ≃ᵢ EPlane) :
    RealPoint.det (frameFirst f) (frameSecond f) ^ 2 = 1 := by
  calc
    RealPoint.det (frameFirst f) (frameSecond f) ^ 2 =
        RealPoint.dot (frameFirst f) (frameFirst f) *
          RealPoint.dot (frameSecond f) (frameSecond f) -
          RealPoint.dot (frameFirst f) (frameSecond f) ^ 2 := by
      simp only [RealPoint.det,RealPoint.dot]
      ring
    _ = 1 := by rw [frame_unit_first,frame_unit_second,frame_orthogonal]; norm_num

theorem frame_second_eq_quarterTurn_or_neg (f : EPlane ≃ᵢ EPlane) :
    frameSecond f = quarterTurn (frameFirst f) ∨
      frameSecond f = -quarterTurn (frameFirst f) := by
  have he := dot_det_decomposition (frameFirst f) (frameSecond f)
  rw [frame_unit_first,frame_orthogonal,one_smul,zero_smul,zero_add] at he
  have hs := frame_determinant_squared f
  have hp : RealPoint.det (frameFirst f) (frameSecond f) = 1 ∨
      RealPoint.det (frameFirst f) (frameSecond f) = -1 := by
    have hz : (RealPoint.det (frameFirst f) (frameSecond f)-1)*
        (RealPoint.det (frameFirst f) (frameSecond f)+1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hp with h | h
  · exact Or.inl (by simpa only [h,one_smul] using he)
  · exact Or.inr (by simpa only [h,neg_one_smul] using he)

def isometryCoefficients (f : EPlane ≃ᵢ EPlane) : RigidCoefficients where
  a := (frameFirst f).1
  b := (frameSecond f).1
  c := (frameFirst f).2
  d := (frameSecond f).2
  u := (euclideanCoordinates.symm (f 0)).1
  v := (euclideanCoordinates.symm (f 0)).2
  row_one := by
    have h := frame_unit_first f
    rcases frame_second_eq_quarterTurn_or_neg f with he | he <;>
      rw [he] <;> simp only [quarterTurn,Prod.fst_neg,neg_sq] <;>
      simpa only [RealPoint.dot,pow_two] using h
  row_two := by
    have h := frame_unit_first f
    simp only [RealPoint.dot] at h
    rcases frame_second_eq_quarterTurn_or_neg f with he | he <;>
      rw [he] <;> simp only [quarterTurn,Prod.snd_neg,neg_sq] <;>
      nlinarith [h]
  row_dot := by
    rcases frame_second_eq_quarterTurn_or_neg f with he | he <;>
      rw [he] <;> simp only [quarterTurn,Prod.fst_neg,Prod.snd_neg] <;> ring

theorem isometry_coefficients_apply (f : EPlane ≃ᵢ EPlane) (x : RealPoint) :
    euclideanCoordinates.symm (f (euclideanCoordinates x)) =
      ((isometryCoefficients f).a*x.1+(isometryCoefficients f).b*x.2+(isometryCoefficients f).u,
       (isometryCoefficients f).c*x.1+(isometryCoefficients f).d*x.2+(isometryCoefficients f).v) := by
  have hx : x = x.1 • ((1,0) : RealPoint) + x.2 • (0,1) := by
    apply Prod.ext <;> simp
  have hlin : coordinateAction f x = x.1 • frameFirst f + x.2 • frameSecond f := by
    conv_lhs => rw [hx,map_add,map_smul,map_smul]
    rfl
  have hoff := coordinateAction_sub f 0 x
  simp only [sub_zero] at hoff
  rw [show euclideanCoordinates (0 : RealPoint) = (0 : EPlane) from coordinateLinearEquiv.map_zero] at hoff
  rw [hlin] at hoff
  apply Prod.ext
  · have h := congrArg Prod.fst hoff
    simp only [Prod.fst_add,Prod.fst_sub,Prod.smul_fst,smul_eq_mul] at h
    change _ = (frameFirst f).1*x.1+(frameSecond f).1*x.2+
      (euclideanCoordinates.symm (f 0)).1
    linarith
  · have h := congrArg Prod.snd hoff
    simp only [Prod.snd_add,Prod.snd_sub,Prod.smul_snd,smul_eq_mul] at h
    change _ = (frameFirst f).2*x.1+(frameSecond f).2*x.2+
      (euclideanCoordinates.symm (f 0)).2
    linarith

theorem isometry_coefficients_determinant (f : EPlane ≃ᵢ EPlane) :
    (isometryCoefficients f).a*(isometryCoefficients f).d-
      (isometryCoefficients f).b*(isometryCoefficients f).c =
        RealPoint.det (frameFirst f) (frameSecond f) := by
  simp only [isometryCoefficients,RealPoint.det]
  ring

end
end LiteralPlanar.Quintic
