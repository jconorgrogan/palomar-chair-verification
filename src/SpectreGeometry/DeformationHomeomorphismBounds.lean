module

public import SpectreGeometry.DeformationHomeomorphism

@[expose] public section


/-! Explicit bi-Lipschitz bounds from the same residual estimate. In
particular, properness and noncollapse need no separate geometric premise. -/
namespace SpectreGeometry.Deformation
noncomputable section
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_bounds_of_eighth_residual (F : E → E)
    (hF : LipschitzWith (15/16 : ℝ≥0) (fun x => x - (1/8 : ℝ) • F x)) (x y : E) :
    ‖x-y‖ ≤ 2 * ‖F x-F y‖ ∧ ‖F x-F y‖ ≤ (31/2 : ℝ) * ‖x-y‖ := by
  let r := (x - (1/8 : ℝ) • F x) - (y - (1/8 : ℝ) • F y)
  have hr : ‖r‖ ≤ (15/16 : ℝ)*‖x-y‖ := by
    simpa only [dist_eq_norm,NNReal.coe_div,NNReal.coe_ofNat] using hF.dist_le_mul x y
  have he : r + (1/8 : ℝ) • (F x-F y) = x-y := by dsimp [r]; rw [smul_sub]; abel
  have hl := norm_add_le r ((1/8 : ℝ) • (F x-F y))
  rw [he,norm_smul] at hl
  have hu := norm_sub_le (x-y) r
  have heu : (x-y)-r = (1/8 : ℝ) • (F x-F y) := by rw [←he]; abel
  rw [heu,norm_smul] at hu
  norm_num [Real.norm_eq_abs] at hl hu
  constructor <;> nlinarith only [hr,hl,hu]

theorem antilipschitz_of_eighth_residual (F : E → E)
    (hF : LipschitzWith (15/16 : ℝ≥0) (fun x => x - (1/8 : ℝ) • F x)) :
    AntilipschitzWith 2 F := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simpa only [dist_eq_norm,NNReal.coe_ofNat] using (norm_bounds_of_eighth_residual F hF x y).1

theorem lipschitz_of_eighth_residual (F : E → E)
    (hF : LipschitzWith (15/16 : ℝ≥0) (fun x => x - (1/8 : ℝ) • F x)) :
    LipschitzWith (31/2 : ℝ≥0) F := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm,NNReal.coe_ofNat,NNReal.coe_div] using (norm_bounds_of_eighth_residual F hF x y).2

end
end SpectreGeometry.Deformation
