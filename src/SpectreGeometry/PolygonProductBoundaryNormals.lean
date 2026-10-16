module

public import SpectreGeometry.PolygonProductConeGerms
public import SpectreGeometry.PolygonBoundaryNormalRank

@[expose] public section


/-! Literal physical edge normals of the two factors in Euclidean4.
The two blocks are orthogonal; within a nonstraight vertex the two incident
normals are independent. No root-normal-plane or angular-mass premise is added. -/
namespace SpectreGeometry
noncomputable section

def leftNormalMap : RealPoint →ₗ[ℝ] EFour :=
  productCoordinateLinearEquiv.toLinearMap.comp (LinearMap.inl ℝ RealPoint RealPoint)

def rightNormalMap : RealPoint →ₗ[ℝ] EFour :=
  productCoordinateLinearEquiv.toLinearMap.comp (LinearMap.inr ℝ RealPoint RealPoint)

def nativeLeftNormal (i : Fin 14) : EFour := leftNormalMap (nativeEdgeNormal i)
def nativeRightNormal (i : Fin 14) : EFour := rightNormalMap (nativeEdgeNormal i)

private theorem leftNormalMap_injective : Function.Injective leftNormalMap :=
  productCoordinateLinearEquiv.injective.comp LinearMap.inl_injective

private theorem rightNormalMap_injective : Function.Injective rightNormalMap :=
  productCoordinateLinearEquiv.injective.comp LinearMap.inr_injective

theorem nativeLeftNormal_ne_zero (i : Fin 14) : nativeLeftNormal i ≠ 0 := by
  intro h
  apply native_edge_normal_ne_zero i
  apply leftNormalMap_injective
  rw [map_zero]
  exact h

theorem nativeRightNormal_ne_zero (i : Fin 14) : nativeRightNormal i ≠ 0 := by
  intro h
  apply native_edge_normal_ne_zero i
  apply rightNormalMap_injective
  rw [map_zero]
  exact h

theorem native_left_normal_inner_vector (i : Fin 14) (v : EFour) :
    inner ℝ (nativeLeftNormal i) v = RealPoint.det (realEdge i) (v 0,v 1) := by
  simp [nativeLeftNormal,leftNormalMap,productCoordinateLinearEquiv,nativeEdgeNormal,
    PiLp.inner_apply,Fin.sum_univ_succ,RealPoint.det,mul_comm] <;> ring

theorem native_right_normal_inner_vector (i : Fin 14) (v : EFour) :
    inner ℝ (nativeRightNormal i) v = RealPoint.det (realEdge i) (v 2,v 3) := by
  simp [nativeRightNormal,rightNormalMap,productCoordinateLinearEquiv,nativeEdgeNormal,
    PiLp.inner_apply,Fin.sum_univ_succ,RealPoint.det,mul_comm] <;> ring

theorem native_product_normals_orthogonal (i j : Fin 14) :
    inner ℝ (nativeLeftNormal i) (nativeRightNormal j) = 0 := by
  rw [native_left_normal_inner_vector]
  simp [nativeRightNormal,rightNormalMap,productCoordinateLinearEquiv,RealPoint.det]

theorem native_left_corner_normals_independent (i : Fin 14) (hi : i ≠ 10) :
    LinearIndependent ℝ ![nativeLeftNormal (previous i),nativeLeftNormal i] := by
  have h := (native_corner_normals_independent i hi).map' leftNormalMap
    (LinearMap.ker_eq_bot.mpr leftNormalMap_injective)
  have he : leftNormalMap ∘ ![nativeEdgeNormal (previous i),nativeEdgeNormal i] =
      ![nativeLeftNormal (previous i),nativeLeftNormal i] := by
    ext k
    fin_cases k <;> rfl
  rw [he] at h
  exact h

theorem native_right_corner_normals_independent (i : Fin 14) (hi : i ≠ 10) :
    LinearIndependent ℝ ![nativeRightNormal (previous i),nativeRightNormal i] := by
  have h := (native_corner_normals_independent i hi).map' rightNormalMap
    (LinearMap.ker_eq_bot.mpr rightNormalMap_injective)
  have he : rightNormalMap ∘ ![nativeEdgeNormal (previous i),nativeEdgeNormal i] =
      ![nativeRightNormal (previous i),nativeRightNormal i] := by
    ext k
    fin_cases k <;> rfl
  rw [he] at h
  exact h

end
end SpectreGeometry
