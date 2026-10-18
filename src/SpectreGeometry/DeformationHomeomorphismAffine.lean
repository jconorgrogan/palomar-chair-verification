module

public import SpectreGeometry.DeformationHomeomorphismMatrix
public import SpectreGeometry.DevelopedRealCoordinates

@[expose] public section


/-! The certified matrices as actual real affine maps, with exact vertex
values and a Euclidean residual Lipschitz estimate. -/
namespace SpectreGeometry.Deformation
noncomputable section
open scoped NNReal

/-- Actual source-frame linear map, distinct for the twelve boundary triangles. -/
def matrixLinearMap (k i : Fin 12) : RealPoint →ₗ[ℝ] RealPoint where
  toFun := matrixLinear k i
  map_add' x y := by
    apply Prod.ext <;> simp only [matrixLinear,Prod.fst_add,Prod.snd_add] <;> ring
  map_smul' c x := by
    apply Prod.ext <;> simp only [matrixLinear,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,RingHom.id_apply] <;> ring

@[simp] theorem matrixLinearMap_apply (k i : Fin 12) (x : RealPoint) :
    matrixLinearMap k i x = matrixLinear k i x := rfl

def matrixEuclideanLinear (k i : Fin 12) : EPlane →ₗ[ℝ] EPlane :=
  coordinateLinearEquiv.toLinearMap.comp ((matrixLinearMap k i).comp coordinateLinearEquiv.symm.toLinearMap)

def residualEuclideanLinear (k i : Fin 12) : EPlane →ₗ[ℝ] EPlane :=
  LinearMap.id - (1/8 : ℝ) • matrixEuclideanLinear k i

theorem matrix_residual_norm_bound (k i : Fin 12) (x : EPlane) :
    ‖residualEuclideanLinear k i x‖ ≤ (15/16 : ℝ) * ‖x‖ := by
  have hh := matrix_residual_squared_bound k i (euclideanCoordinates.symm x)
  have he : euclideanCoordinates.symm (residualEuclideanLinear k i x) =
      euclideanCoordinates.symm x - (1/8 : ℝ) • matrixLinear k i (euclideanCoordinates.symm x) := by
    change coordinateLinearEquiv.symm (x - (1/8 : ℝ) •
      coordinateLinearEquiv (matrixLinearMap k i (coordinateLinearEquiv.symm x))) = _
    rw [map_sub,map_smul,coordinateLinearEquiv.symm_apply_apply]
    rfl
  rw [←he,coordinate_dot_norm_squared,coordinate_dot_norm_squared] at hh
  nlinarith [norm_nonneg (residualEuclideanLinear k i x),norm_nonneg x]

theorem residualEuclideanLinear_lipschitz (k i : Fin 12) :
    LipschitzWith (15/16 : ℝ≥0) (residualEuclideanLinear k i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm,←map_sub]
  norm_num only [NNReal.coe_div,NNReal.coe_ofNat]
  exact matrix_residual_norm_bound k i (x-y)

theorem sourceVertex4_eval (k : Fin 12) (e : Fin 14) :
    ExactPoint.eval (sourceVertex4 k e) = (4 : ℝ) • rotate k (realVertex e) := by
  apply Prod.ext <;>
    simp only [sourceVertex4,ExactPoint.eval,complexMulExact,Quad3.eval_add,Quad3.eval_sub,
      Quad3.eval_mul,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,rotate,complexMulReal,
      realDirection,realVertex,realize] <;> ring

theorem targetVertex4_eval (k : Fin 12) (e : Fin 14) :
    ExactPoint.eval (targetVertex4 k e) = (4 : ℝ) • realDeformedVertex k e := by
  apply Prod.ext <;>
    simp only [targetVertex4,ExactPoint.eval,Quad3.eval,realDeformedVertex,kiteCoordinateEmbedding,
      rationalKitePoint,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Int.cast_zero,Int.cast_mul,
      Int.cast_ofNat,Int.cast_add,Rat.cast_intCast,zero_add,mul_zero,add_zero] <;> ring

theorem matrixLinearMap_sourceColumn (k i : Fin 12) (second : Bool) :
    matrixLinearMap k i (ExactPoint.eval (sourceColumn k i second)) =
      ExactPoint.eval (targetColumn k i second) := by
  have hd : Quad3.eval (sourceDet k i) ≠ 0 := ne_of_gt (sourceDet_pos k i)
  cases second <;> apply Prod.ext <;>
    simp only [matrixLinearMap_apply,matrixLinear,numeratorMatrix,ExactPoint.eval,
      Quad3.eval_sub,Quad3.eval_mul] <;> field_simp [hd] <;>
    simp only [sourceDet,ExactPoint.eval_det,RealPoint.det,ExactPoint.eval] <;> ring


theorem sourceColumn_eval (k i : Fin 12) (second : Bool) :
    ExactPoint.eval (sourceColumn k i second) = (4 : ℝ) •
      (rotate k (realVertex (if second then (triangle i).2.2 else (triangle i).2.1)) -
        rotate k (realVertex (triangle i).1)) := by
  rw [sourceColumn,ExactPoint.eval_sub,sourceVertex4_eval,sourceVertex4_eval]
  apply Prod.ext <;> simp only [RealPoint.sub,Prod.smul_fst,Prod.smul_snd,
    Prod.fst_sub,Prod.snd_sub,smul_eq_mul] <;> ring

theorem targetColumn_eval (k i : Fin 12) (second : Bool) :
    ExactPoint.eval (targetColumn k i second) = (4 : ℝ) •
      (realDeformedVertex k (if second then (triangle i).2.2 else (triangle i).2.1) -
        realDeformedVertex k (triangle i).1) := by
  rw [targetColumn,ExactPoint.eval_sub,targetVertex4_eval,targetVertex4_eval]
  apply Prod.ext <;> simp only [RealPoint.sub,Prod.smul_fst,Prod.smul_snd,
    Prod.fst_sub,Prod.snd_sub,smul_eq_mul] <;> ring

theorem matrixLinearMap_vertexDifference (k i : Fin 12) (second : Bool) :
    matrixLinearMap k i
      (rotate k (realVertex (if second then (triangle i).2.2 else (triangle i).2.1)) -
        rotate k (realVertex (triangle i).1)) =
      realDeformedVertex k (if second then (triangle i).2.2 else (triangle i).2.1) -
        realDeformedVertex k (triangle i).1 := by
  have h := matrixLinearMap_sourceColumn k i second
  rw [sourceColumn_eval,targetColumn_eval,map_smul] at h
  have hh := congrArg (fun v : RealPoint => (1/4 : ℝ) • v) h
  simpa only [smul_smul,show (1/4 : ℝ)*4=1 by norm_num,one_smul] using hh

def triangleAffine (k i : Fin 12) : RealPoint →ᵃ[ℝ] RealPoint where
  toFun x := realDeformedVertex k (triangle i).1 +
    matrixLinearMap k i (x - rotate k (realVertex (triangle i).1))
  linear := matrixLinearMap k i
  map_vadd' p v := by
    simp only [vadd_eq_add,map_sub,map_add]
    abel

@[simp] theorem triangleAffine_apply (k i : Fin 12) (x : RealPoint) :
    triangleAffine k i x = realDeformedVertex k (triangle i).1 +
      matrixLinearMap k i (x - rotate k (realVertex (triangle i).1)) := rfl

theorem triangleAffine_first (k i : Fin 12) :
    triangleAffine k i (rotate k (realVertex (triangle i).1)) =
      realDeformedVertex k (triangle i).1 := by
  rw [triangleAffine_apply,sub_self,map_zero,add_zero]

theorem triangleAffine_other (k i : Fin 12) (second : Bool) :
    triangleAffine k i
      (rotate k (realVertex (if second then (triangle i).2.2 else (triangle i).2.1))) =
      realDeformedVertex k (if second then (triangle i).2.2 else (triangle i).2.1) := by
  rw [triangleAffine_apply,matrixLinearMap_vertexDifference]
  abel


def affineEuclidean (k i : Fin 12) (a b : EPlane) (x : EPlane) : EPlane :=
  b + matrixEuclideanLinear k i (x-a)

theorem affineEuclidean_residual_lipschitz (k i : Fin 12) (a b : EPlane) :
    LipschitzWith (15/16 : ℝ≥0) (fun x => x - (1/8 : ℝ) • affineEuclidean k i a b x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  have he : (x - (1/8 : ℝ) • affineEuclidean k i a b x) -
      (y - (1/8 : ℝ) • affineEuclidean k i a b y) = residualEuclideanLinear k i (x-y) := by
    simp only [affineEuclidean,residualEuclideanLinear,LinearMap.sub_apply,LinearMap.id_apply,
      LinearMap.smul_apply,map_sub,smul_add,smul_sub]
    abel
  rw [he]
  norm_num only [NNReal.coe_div,NNReal.coe_ofNat]
  exact matrix_residual_norm_bound k i (x-y)

end
end SpectreGeometry.Deformation
