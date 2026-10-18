module

public import SpectreGeometry.PolygonProductBoundaryNormals
public import SpectreGeometry.PolygonBoundaryNormalAngles

@[expose] public section


namespace SpectreGeometry
noncomputable section

def leftBlockLinear : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EFour where
  toFun x := WithLp.toLp 2 ![x 0,x 1,0,0]
  map_add' := by intro x y; ext i; fin_cases i <;> simp
  map_smul' := by intro a x; ext i; fin_cases i <;> simp

def rightBlockLinear : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EFour where
  toFun x := WithLp.toLp 2 ![0,0,x 0,x 1]
  map_add' := by intro x y; ext i; fin_cases i <;> simp
  map_smul' := by intro a x; ext i; fin_cases i <;> simp

def leftBlockIsometry : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour :=
  leftBlockLinear.isometryOfInner (by
    intro x y
    simp [leftBlockLinear,PiLp.inner_apply,Fin.sum_univ_succ])

def rightBlockIsometry : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour :=
  rightBlockLinear.isometryOfInner (by
    intro x y
    simp [rightBlockLinear,PiLp.inner_apply,Fin.sum_univ_succ])

theorem nativeLeftNormal_eq_block (i : Fin 14) :
    nativeLeftNormal i = leftBlockIsometry (nativeEuclideanEdgeNormal i) := rfl

theorem nativeRightNormal_eq_block (i : Fin 14) :
    nativeRightNormal i = rightBlockIsometry (nativeEuclideanEdgeNormal i) := rfl

def factorNormal (right : Bool) (i : Fin 14) : EFour :=
  if right then nativeRightNormal i else nativeLeftNormal i

def factorProjection (right : Bool) (v : EFour) : RealPoint :=
  if right then (v 2,v 3) else (v 0,v 1)

theorem factorNormal_ne_zero (right : Bool) (i : Fin 14) : factorNormal right i ≠ 0 := by
  cases right
  · exact nativeLeftNormal_ne_zero i
  · exact nativeRightNormal_ne_zero i

theorem factorNormal_inner_vector (right : Bool) (i : Fin 14) (v : EFour) :
    inner ℝ (factorNormal right i) v = RealPoint.det (realEdge i) (factorProjection right v) := by
  cases right
  · exact native_left_normal_inner_vector i v
  · exact native_right_normal_inner_vector i v

theorem factorNormal_adjacent_angle (right : Bool) (i : Fin 14) :
    InnerProductGeometry.angle (factorNormal right (previous i)) (factorNormal right i) =
      InnerProductGeometry.angle (nativeEuclideanEdgeNormal (previous i))
        (nativeEuclideanEdgeNormal i) := by
  cases right
  · change InnerProductGeometry.angle (nativeLeftNormal _) (nativeLeftNormal _) = _
    rw [nativeLeftNormal_eq_block,nativeLeftNormal_eq_block]
    exact leftBlockIsometry.angle_map _ _
  · change InnerProductGeometry.angle (nativeRightNormal _) (nativeRightNormal _) = _
    rw [nativeRightNormal_eq_block,nativeRightNormal_eq_block]
    exact rightBlockIsometry.angle_map _ _

end
end SpectreGeometry
