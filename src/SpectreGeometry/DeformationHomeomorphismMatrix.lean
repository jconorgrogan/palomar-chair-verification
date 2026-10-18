module

public import SpectreGeometry.DeformationHomeomorphismData
public import SpectreGeometry.CyclicRotations
public import Mathlib.Tactic.FieldSimp

@[expose] public section


/-! Real soundness of the exact residual-matrix certificates. -/
namespace SpectreGeometry.Deformation
noncomputable section

def matrixLinear (k i : Fin 12) (x : RealPoint) : RealPoint :=
  let n := numeratorMatrix k i
  let d := Quad3.eval (sourceDet k i)
  ((Quad3.eval n.1*x.1+Quad3.eval n.2.1*x.2)/d,
    (Quad3.eval n.2.2.1*x.1+Quad3.eval n.2.2.2*x.2)/d)

theorem sourceDet_pos (k i : Fin 12) : 0 < Quad3.eval (sourceDet k i) :=
  Quad3.positive_sound _ (residual_matrix_certificate k i).1

private theorem quadratic_form_nonneg (a b c x y : ℝ) (ha : 0 < a)
    (hdet : 0 ≤ a*c-b*b) : 0 ≤ a*x*x+2*b*x*y+c*y*y := by
  have h1 : 0 ≤ (a*x+b*y)^2 := sq_nonneg _
  have h2 : 0 ≤ (a*c-b*b)*y^2 := mul_nonneg hdet (sq_nonneg _)
  have hid : a*(a*x*x+2*b*x*y+c*y*y) = (a*x+b*y)^2+(a*c-b*b)*y^2 := by ring
  have hh : 0 ≤ a*(a*x*x+2*b*x*y+c*y*y) := by rw [hid]; positivity
  exact nonneg_of_mul_nonneg_right hh ha

/-- The literal finite matrix certificate implies the ordinary Euclidean
squared-norm bound with residual constant 15/16. -/
theorem matrix_residual_squared_bound (k i : Fin 12) (x : RealPoint) :
    RealPoint.dot (x - (1/8 : ℝ) • matrixLinear k i x)
        (x - (1/8 : ℝ) • matrixLinear k i x) ≤
      (15/16 : ℝ)^2 * RealPoint.dot x x := by
  let r := residualMatrix k i
  let d := Quad3.eval (sourceDet k i)
  let a := Quad3.eval r.1
  let b := Quad3.eval r.2.1
  let c := Quad3.eval r.2.2.1
  let e := Quad3.eval r.2.2.2
  have hd : 0 < d := sourceDet_pos k i
  have hc := residual_matrix_certificate k i
  have h11 := Quad3.positive_sound _ hc.2.1
  have hdet := Quad3.positive_sound _ hc.2.2
  simp only [residualGramGap,Quad3.eval_sub,Quad3.eval_add,Quad3.eval_mul] at h11 hdet
  norm_num [Quad3.eval] at h11 hdet
  have h11' : 0 < 225*d*d-4*(a*a+c*c) := by
    dsimp [d,a,c,r,Quad3.eval]
    nlinarith only [h11]
  have hdet' : 0 < (225*d*d-4*(a*a+c*c))*(225*d*d-4*(b*b+e*e))-
      (-(4*(a*b+c*e)))*(-(4*(a*b+c*e))) := by
    dsimp [d,a,b,c,e,r,Quad3.eval]
    nlinarith only [hdet]
  have hq := quadratic_form_nonneg (225*d*d-4*(a*a+c*c)) (-(4*(a*b+c*e)))
    (225*d*d-4*(b*b+e*e)) x.1 x.2 h11' hdet'.le
  have hh : 4*((a*x.1+b*x.2)^2+(c*x.1+e*x.2)^2) ≤
      225*d*d*(x.1*x.1+x.2*x.2) := by nlinarith only [hq]
  have heq : x - (1/8 : ℝ) • matrixLinear k i x =
      ((a*x.1+b*x.2)/(8*d),(c*x.1+e*x.2)/(8*d)) := by
    have hd0 : Quad3.eval (sourceDet k i) ≠ 0 := ne_of_gt (sourceDet_pos k i)
    apply Prod.ext <;>
      simp only [Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
        matrixLinear,a,b,c,e,r,d,residualMatrix,Quad3.eval_sub,Quad3.eval_mul,
        show Quad3.eval (8,0) = 8 by norm_num [Quad3.eval],
        show Quad3.eval (0,0) = 0 by norm_num [Quad3.eval]] <;>
      field_simp [hd0] <;> ring
  rw [heq]
  simp only [RealPoint.dot]
  have hh' := div_le_div_of_nonneg_right hh (show (0 : ℝ) ≤ 256*d*d by positivity)
  convert hh' using 1 <;> field_simp [ne_of_gt hd] <;> ring

end
end SpectreGeometry.Deformation
