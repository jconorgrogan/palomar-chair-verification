module

public import SpectreGeometry.UnitEdgeDirections
public import SpectreGeometry.CyclicRotations

@[expose] public section


/-! Continuous, unrestricted direct Euclidean isometries expressed by their
actual linear frame. No discreteness of the rotation is assumed. -/
namespace SpectreGeometry
noncomputable section

def coordinateAction (f : EPlane ≃ᵢ EPlane) : RealPoint ≃ₗ[ℝ] RealPoint :=
  coordinateLinearEquiv.trans (f.toRealLinearIsometryEquiv.toLinearEquiv.trans coordinateLinearEquiv.symm)

def frameFirst (f : EPlane ≃ᵢ EPlane) : RealPoint := coordinateAction f (1,0)
def frameSecond (f : EPlane ≃ᵢ EPlane) : RealPoint := coordinateAction f (0,1)

/-- Positivity of the determinant of the actual linear part; no finite
rotation enumeration is built into this direct-placement predicate. -/
def DirectPlacement (f : EPlane ≃ᵢ EPlane) : Prop :=
  0 < RealPoint.det (frameFirst f) (frameSecond f)

theorem coordinateAction_dot_self (f : EPlane ≃ᵢ EPlane) (x : RealPoint) :
    RealPoint.dot (coordinateAction f x) (coordinateAction f x) = RealPoint.dot x x := by
  have hh := coordinate_dot_norm_squared (f.toRealLinearIsometryEquiv (coordinateLinearEquiv x))
  rw [LinearIsometryEquiv.norm_map] at hh
  have hx := coordinate_dot_norm_squared (coordinateLinearEquiv x)
  change RealPoint.dot x x = _ at hx
  exact hh.trans hx.symm

theorem coordinateAction_dot (f : EPlane ≃ᵢ EPlane) (x y : RealPoint) :
    RealPoint.dot (coordinateAction f x) (coordinateAction f y) = RealPoint.dot x y := by
  have hx := coordinateAction_dot_self f x
  have hy := coordinateAction_dot_self f y
  have hs := coordinateAction_dot_self f (x+y)
  rw [map_add] at hs
  simp only [RealPoint.dot,Prod.fst_add,Prod.snd_add] at *
  nlinarith

theorem frame_unit_first (f : EPlane ≃ᵢ EPlane) : RealPoint.dot (frameFirst f) (frameFirst f) = 1 := by
  simpa [frameFirst,RealPoint.dot] using coordinateAction_dot_self f (1,0)

theorem frame_unit_second (f : EPlane ≃ᵢ EPlane) : RealPoint.dot (frameSecond f) (frameSecond f) = 1 := by
  simpa [frameSecond,RealPoint.dot] using coordinateAction_dot_self f (0,1)

theorem frame_orthogonal (f : EPlane ≃ᵢ EPlane) : RealPoint.dot (frameFirst f) (frameSecond f) = 0 := by
  simpa [frameFirst,frameSecond,RealPoint.dot] using coordinateAction_dot f (1,0) (0,1)

theorem orthogonal_positive_quarterTurn (a b : RealPoint)
    (ha : RealPoint.dot a a = 1) (hb : RealPoint.dot b b = 1)
    (hab : RealPoint.dot a b = 0) (hp : 0 < RealPoint.det a b) : b = quarterTurn a := by
  have he := dot_det_decomposition a b
  rw [ha,hab,one_smul,zero_smul,zero_add] at he
  have hqa : RealPoint.dot (quarterTurn a) (quarterTurn a) = 1 := by
    simpa only [quarterTurn,RealPoint.dot,neg_mul_neg,add_comm] using ha
  have hs : RealPoint.det a b ^ 2 = 1 := by
    calc
      RealPoint.det a b ^ 2 = RealPoint.det a b ^ 2 * RealPoint.dot (quarterTurn a) (quarterTurn a) := by rw [hqa,mul_one]
      _ = RealPoint.dot (RealPoint.det a b • quarterTurn a) (RealPoint.det a b • quarterTurn a) :=
        (dot_smul_self _ _).symm
      _ = 1 := by rw [←he,hb]
  have hdet : RealPoint.det a b = 1 := by nlinarith
  simpa [hdet] using he

theorem direct_frame_second (f : EPlane ≃ᵢ EPlane) (hf : DirectPlacement f) :
    frameSecond f = quarterTurn (frameFirst f) :=
  orthogonal_positive_quarterTurn _ _ (frame_unit_first f) (frame_unit_second f) (frame_orthogonal f) hf

/-- Every direct isometry has the expected complex-multiplication linear
part, derived from its genuine orthonormal frame. -/
theorem direct_coordinateAction (f : EPlane ≃ᵢ EPlane) (hf : DirectPlacement f) (x : RealPoint) :
    coordinateAction f x = complexMulReal (frameFirst f) x := by
  have hx : x = x.1 • ((1,0) : RealPoint) + x.2 • (0,1) := by
    apply Prod.ext <;> simp
  have hlin : coordinateAction f x = x.1 • frameFirst f + x.2 • frameSecond f := by
    conv_lhs => rw [hx,map_add,map_smul,map_smul]
    rfl
  rw [hlin,direct_frame_second f hf]
  apply Prod.ext <;> simp only [complexMulReal,quarterTurn,Prod.smul_fst,Prod.smul_snd,
    Prod.fst_add,Prod.snd_add,smul_eq_mul] <;> ring

theorem coordinateAction_sub (f : EPlane ≃ᵢ EPlane) (x y : RealPoint) :
    coordinateAction f (y-x) = euclideanCoordinates.symm (f (euclideanCoordinates y)) -
      euclideanCoordinates.symm (f (euclideanCoordinates x)) := by
  have he : f.toRealLinearIsometryEquiv (coordinateLinearEquiv (y-x)) =
      f (euclideanCoordinates y)-f (euclideanCoordinates x) := by
    rw [map_sub,map_sub,IsometryEquiv.toRealLinearIsometryEquiv_apply,
      IsometryEquiv.toRealLinearIsometryEquiv_apply]
    change (f (euclideanCoordinates y)-f 0)-(f (euclideanCoordinates x)-f 0) = _
    abel
  change coordinateLinearEquiv.symm (f.toRealLinearIsometryEquiv (coordinateLinearEquiv (y-x))) = _
  rw [he,map_sub]
  rfl

theorem coordinateAction_edge (f : EPlane ≃ᵢ EPlane) (i : Fin 14) :
    coordinateAction f (realEdge i) = euclideanCoordinates.symm (placedEdgeVector f i) := by
  have h := coordinateAction_sub f (realVertex i) (realVertex (next i))
  change coordinateAction f (realEdge i) = _ at h
  rw [h]
  change coordinateLinearEquiv.symm (f (euclideanVertex (next i))) -
    coordinateLinearEquiv.symm (f (euclideanVertex i)) =
      coordinateLinearEquiv.symm (f (euclideanVertex (next i))-f (euclideanVertex i))
  exact (map_sub _ _ _).symm

end
end SpectreGeometry
