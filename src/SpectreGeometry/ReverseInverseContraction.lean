module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! A Hilbert-space residual bound controls inverse charts with the same
strict contraction constant. This can reuse the checked forward deformation
matrices on an independently constructed H/T tiling. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inversion of the operator disk centered at the identity. The constants
are exact: 1-(15/16)^2=31/256. No inverse map is assumed in this lemma. -/
theorem reverse_residual_norm (x y : E)
    (h : ‖x-y‖ ≤ (15/16 : ℝ)*‖x‖) :
    ‖y-(31/256 : ℝ) • x‖ ≤ (15/16 : ℝ)*‖y‖ := by
  have hs : ‖x-y‖^2 ≤ (15/16 : ℝ)^2*‖x‖^2 := by
    nlinarith [norm_nonneg (x-y),norm_nonneg x]
  have hxy := norm_sub_sq_real x y
  have hyx := norm_sub_sq_real y ((31/256 : ℝ) • x)
  rw [real_inner_smul_right,norm_smul,Real.norm_eq_abs,real_inner_comm x y] at hyx
  norm_num at hyx
  have ht : ‖y-(31/256 : ℝ) • x‖^2 ≤ (15/16 : ℝ)^2*‖y‖^2 := by
    nlinarith
  nlinarith [norm_nonneg (y-(31/256 : ℝ) • x),norm_nonneg y]

/-- Applied to a forward chart A with residual scale1/8, the inverse residual
uses scale31/32 and keeps the strict constant15/16. -/
theorem reverse_deformation_residual (x y : E)
    (h : ‖x-(1/8 : ℝ) • y‖ ≤ (15/16 : ℝ)*‖x‖) :
    ‖y-(31/32 : ℝ) • x‖ ≤ (15/16 : ℝ)*‖y‖ := by
  have hr := reverse_residual_norm x ((1/8 : ℝ) • y) h
  have he : y-(31/32 : ℝ) • x =
      (8 : ℝ) • ((1/8 : ℝ) • y-(31/256 : ℝ) • x) := by
    rw [smul_sub,smul_smul,smul_smul]
    norm_num
  rw [he,norm_smul,Real.norm_eq_abs]
  rw [norm_smul,Real.norm_eq_abs] at hr
  norm_num at hr ⊢
  linarith

/-- Any actual inverse pair inherits a Lipschitz residual estimate. The maps
need not be linear; the forward estimate is used on inverse-point differences. -/
theorem inverse_residual_lipschitz (F G : E → E)
    (hFG : ∀ x, F (G x) = x)
    (hF : LipschitzWith (15/16 : ℝ≥0) (fun x => x-(1/8 : ℝ) • F x)) :
    LipschitzWith (15/16 : ℝ≥0) (fun x => x-(31/32 : ℝ) • G x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hF.dist_le_mul (G x) (G y)
  rw [dist_eq_norm,dist_eq_norm,hFG,hFG] at h
  have hsrc : ‖(G x-G y)-(1/8 : ℝ) • (x-y)‖ ≤ (15/16 : ℝ)*‖G x-G y‖ := by
    have he : (G x-(1/8 : ℝ) • x)-(G y-(1/8 : ℝ) • y) =
        (G x-G y)-(1/8 : ℝ) • (x-y) := by rw [smul_sub]; abel
    simpa only [he,NNReal.coe_div,NNReal.coe_ofNat] using h
  have hr := reverse_deformation_residual (G x-G y) (x-y) hsrc
  rw [dist_eq_norm,dist_eq_norm]
  have he : (x-(31/32 : ℝ) • G x)-(y-(31/32 : ℝ) • G y) =
      (x-y)-(31/32 : ℝ) • (G x-G y) := by rw [smul_sub]; abel
  simpa only [he,NNReal.coe_div,NNReal.coe_ofNat] using hr

/-- The same estimate applies to a chart inverse defined only on its actual
closed target carrier. Compatibility between different charts is separate. -/
theorem inverse_residual_lipschitzOn (F G : E → E) (s : Set E)
    (hFG : ∀ x ∈ s, F (G x) = x)
    (hF : LipschitzWith (15/16 : ℝ≥0) (fun x => x-(1/8 : ℝ) • F x)) :
    LipschitzOnWith (15/16 : ℝ≥0) (fun x => x-(31/32 : ℝ) • G x) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := hF.dist_le_mul (G x) (G y)
  rw [dist_eq_norm,dist_eq_norm,hFG x hx,hFG y hy] at h
  have hsrc : ‖(G x-G y)-(1/8 : ℝ) • (x-y)‖ ≤ (15/16 : ℝ)*‖G x-G y‖ := by
    have he : (G x-(1/8 : ℝ) • x)-(G y-(1/8 : ℝ) • y) =
        (G x-G y)-(1/8 : ℝ) • (x-y) := by rw [smul_sub]; abel
    simpa only [he,NNReal.coe_div,NNReal.coe_ofNat] using h
  have hr := reverse_deformation_residual (G x-G y) (x-y) hsrc
  rw [dist_eq_norm,dist_eq_norm]
  have he : (x-(31/32 : ℝ) • G x)-(y-(31/32 : ℝ) • G y) =
      (x-y)-(31/32 : ℝ) • (G x-G y) := by rw [smul_sub]; abel
  simpa only [he,NNReal.coe_div,NNReal.coe_ofNat] using hr

end
end SpectreGeometry.ReverseExistence
