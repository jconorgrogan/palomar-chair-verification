module

public import SpectreGeometry.ReverseIntegerInterpolation
public import SpectreGeometry.DeformationHomeomorphism

@[expose] public section


/-! Quantitative global inversion of an actual anchor interpolation.
Four uniform neighboring-difference bounds suffice; no injectivity, properness,
or plane-coverage premise is supplied. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set
open scoped NNReal

abbrev AnchorPlane := ℝ × ℝ

def anchorInterpolation (A : ℤ × ℤ → AnchorPlane) (x : AnchorPlane) : AnchorPlane :=
  (gridInterpolate (fun p => (A p).1) x,gridInterpolate (fun p => (A p).2) x)

structure AnchorResidualBounds (A : ℤ × ℤ → AnchorPlane) : Prop where
  horizontal_first : ∀ n m, |1-((A (n+1,m)).1-(A (n,m)).1)/16| ≤ (1/2:ℝ)
  vertical_first : ∀ n m, |((A (n,m+1)).1-(A (n,m)).1)/16| ≤ (3/8:ℝ)
  horizontal_second : ∀ n m, |((A (n+1,m)).2-(A (n,m)).2)/16| ≤ (3/8:ℝ)
  vertical_second : ∀ n m, |1-((A (n,m+1)).2-(A (n,m)).2)/16| ≤ (5/8:ℝ)

def residualFirst (A : ℤ × ℤ → AnchorPlane) (p : ℤ × ℤ) : ℝ := p.1-(A p).1/16
def residualSecond (A : ℤ × ℤ → AnchorPlane) (p : ℤ × ℤ) : ℝ := p.2-(A p).2/16

theorem gridInterpolate_two_coordinate_bound (a : ℤ × ℤ → ℝ) (K L : ℝ≥0)
    (hK : ∀ n m, |a (n+1,m)-a (n,m)| ≤ K)
    (hL : ∀ n m, |a (n,m+1)-a (n,m)| ≤ L) (x y : AnchorPlane) :
    dist (gridInterpolate a x) (gridInterpolate a y) ≤
      K*dist x.1 y.1+L*dist x.2 y.2 := by
  calc
    _ ≤ dist (gridInterpolate a x) (gridInterpolate a (y.1,x.2))+
        dist (gridInterpolate a (y.1,x.2)) (gridInterpolate a y) := dist_triangle _ _ _
    _ ≤ _ := add_le_add ((gridInterpolate_horizontal a K hK x.2).dist_le_mul x.1 y.1)
      ((gridInterpolate_vertical a L hL y.1).dist_le_mul x.2 y.2)

private theorem residualFirst_bounds (A : ℤ × ℤ → AnchorPlane) (hA : AnchorResidualBounds A) :
    (∀ n m, |residualFirst A (n+1,m)-residualFirst A (n,m)| ≤ (1/2:ℝ)) ∧
    (∀ n m, |residualFirst A (n,m+1)-residualFirst A (n,m)| ≤ (3/8:ℝ)) := by
  constructor
  · intro n m
    convert hA.horizontal_first n m using 1 <;> simp [residualFirst] <;> congr 1 <;> ring
  · intro n m
    have he : residualFirst A (n,m+1)-residualFirst A (n,m) =
        -(((A (n,m+1)).1-(A (n,m)).1)/16) := by simp [residualFirst]; ring
    rw [he,abs_neg]
    exact hA.vertical_first n m

private theorem residualSecond_bounds (A : ℤ × ℤ → AnchorPlane) (hA : AnchorResidualBounds A) :
    (∀ n m, |residualSecond A (n+1,m)-residualSecond A (n,m)| ≤ (3/8:ℝ)) ∧
    (∀ n m, |residualSecond A (n,m+1)-residualSecond A (n,m)| ≤ (5/8:ℝ)) := by
  constructor
  · intro n m
    have he : residualSecond A (n+1,m)-residualSecond A (n,m) =
        -(((A (n+1,m)).2-(A (n,m)).2)/16) := by simp [residualSecond]; ring
    rw [he,abs_neg]
    exact hA.horizontal_second n m
  · intro n m
    convert hA.vertical_second n m using 1 <;> simp [residualSecond] <;> congr 1 <;> ring

def rescalePlane : AnchorPlane ≃ₜ AnchorPlane where
  toFun x := (x.1,5/6*x.2)
  invFun x := (x.1,6/5*x.2)
  left_inv x := by ext <;> simp <;> ring
  right_inv x := by ext <;> simp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def scaledAnchorMap (A : ℤ × ℤ → AnchorPlane) (x : AnchorPlane) : AnchorPlane :=
  rescalePlane (anchorInterpolation A (rescalePlane.symm x))

private theorem scaled_residual_formula (A : ℤ × ℤ → AnchorPlane) (x : AnchorPlane) :
    x-(1/16:ℝ) • scaledAnchorMap A x =
      (gridInterpolate (residualFirst A) (x.1,6/5*x.2),
        5/6*gridInterpolate (residualSecond A) (x.1,6/5*x.2)) := by
  have h1 : gridInterpolate (residualFirst A) (x.1,6/5*x.2) =
      x.1-gridInterpolate (fun p => (A p).1) (x.1,6/5*x.2)/16 := by
    unfold residualFirst
    simp only [div_eq_mul_inv,←mul_comm (16:ℝ)⁻¹,
      gridInterpolate_sub,gridInterpolate_smul,gridInterpolate_fst]
  have h2 : gridInterpolate (residualSecond A) (x.1,6/5*x.2) =
      6/5*x.2-gridInterpolate (fun p => (A p).2) (x.1,6/5*x.2)/16 := by
    unfold residualSecond
    simp only [div_eq_mul_inv,←mul_comm (16:ℝ)⁻¹,
      gridInterpolate_sub,gridInterpolate_smul,gridInterpolate_snd]
  rw [h1,h2]
  apply Prod.ext <;> simp [scaledAnchorMap,rescalePlane,anchorInterpolation] <;> ring

theorem scaledAnchorMap_residual_lipschitz (A : ℤ × ℤ → AnchorPlane)
    (hA : AnchorResidualBounds A) :
    LipschitzWith (19/20:ℝ≥0) (fun x => x-(1/16:ℝ) • scaledAnchorMap A x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [scaled_residual_formula,scaled_residual_formula,Prod.dist_eq]
  apply max_le
  · have h := gridInterpolate_two_coordinate_bound (residualFirst A) (1/2) (3/8)
      (residualFirst_bounds A hA).1 (residualFirst_bounds A hA).2
      (x.1,6/5*x.2) (y.1,6/5*y.2)
    have hx : dist x.1 y.1 ≤ dist x y := le_max_left _ _
    have hy : dist x.2 y.2 ≤ dist x y := le_max_right _ _
    have he : dist (6/5*x.2) (6/5*y.2) = (6/5:ℝ)*dist x.2 y.2 := by
      simp only [Real.dist_eq,←mul_sub,abs_mul]
      norm_num
    simp only [he,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one] at h ⊢
    nlinarith
  · have h := gridInterpolate_two_coordinate_bound (residualSecond A) (3/8) (5/8)
      (residualSecond_bounds A hA).1 (residualSecond_bounds A hA).2
      (x.1,6/5*x.2) (y.1,6/5*y.2)
    have hx : dist x.1 y.1 ≤ dist x y := le_max_left _ _
    have hy : dist x.2 y.2 ≤ dist x y := le_max_right _ _
    have he : dist (6/5*x.2) (6/5*y.2) = (6/5:ℝ)*dist x.2 y.2 := by
      simp only [Real.dist_eq,←mul_sub,abs_mul]
      norm_num
    have hscale (u v : ℝ) : dist ((5/6:ℝ)*u) ((5/6:ℝ)*v) = (5/6:ℝ)*dist u v := by
      simp only [Real.dist_eq,←mul_sub,abs_mul]
      norm_num
    rw [hscale]
    simp only [he,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one] at h ⊢
    nlinarith [show (0:ℝ) ≤ dist x y from dist_nonneg]

def scaledAnchorHomeomorph (A : ℤ × ℤ → AnchorPlane) (hA : AnchorResidualBounds A) :
    AnchorPlane ≃ₜ AnchorPlane :=
  (Deformation.identitySubHomeomorph (fun x => x-(1/16:ℝ) • scaledAnchorMap A x)
    (19/20) (by norm_num) (scaledAnchorMap_residual_lipschitz A hA)).trans
      (Homeomorph.smulOfNeZero (16:ℝ) (by norm_num))

@[simp] theorem scaledAnchorHomeomorph_apply (A : ℤ × ℤ → AnchorPlane)
    (hA : AnchorResidualBounds A) (x : AnchorPlane) :
    scaledAnchorHomeomorph A hA x = scaledAnchorMap A x := by
  simp [scaledAnchorHomeomorph,smul_smul]

/-- A globally defined homeomorphism built from the anchor data. This gives
properness and injectivity of the interpolation without either as a premise. -/
def anchorHomeomorph (A : ℤ × ℤ → AnchorPlane) (hA : AnchorResidualBounds A) :
    AnchorPlane ≃ₜ AnchorPlane :=
  rescalePlane.trans ((scaledAnchorHomeomorph A hA).trans rescalePlane.symm)

@[simp] theorem anchorHomeomorph_apply (A : ℤ × ℤ → AnchorPlane)
    (hA : AnchorResidualBounds A) (x : AnchorPlane) :
    anchorHomeomorph A hA x = anchorInterpolation A x := by
  simp [anchorHomeomorph,scaledAnchorMap]

@[simp] theorem anchorHomeomorph_integer (A : ℤ × ℤ → AnchorPlane)
    (hA : AnchorResidualBounds A) (n m : ℤ) :
    anchorHomeomorph A hA (n,m) = A (n,m) := by
  simp [anchorInterpolation]

end
end SpectreGeometry.ReverseExistence
