module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section


/-! A reusable geometric angle bound for shallow key-face normals. These
theorems concern actual vector angles. Binding a concrete keyed body to these
normals is a separate geometric obligation. -/
namespace SpectreGeometry.KeyNormalTwelfthAngle
open scoped InnerProductSpace
open InnerProductGeometry
noncomputable section

theorem cos_pi_div_twelve_sq_lt :
    Real.cos (Real.pi / 12) ^ 2 < (15 : ℝ) / 16 := by
  have h := Real.cos_two_mul (Real.pi / 12)
  have ha : 2 * (Real.pi / 12) = Real.pi / 6 := by ring
  rw [ha, Real.cos_pi_div_six] at h
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  have hroot : Real.sqrt 3 < (7 : ℝ) / 4 := by nlinarith
  nlinarith

/-- Positive, nonparallel normals with squared normalized dot product above
15/16 have a genuine nonzero angle strictly below pi/12. -/
theorem geometric_normal_angle_lt_pi_div_twelve {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v w : E)
    (hip : 0 < inner ℝ v w)
    (hSq : (15 : ℝ) / 16 < (inner ℝ v w / (‖v‖ * ‖w‖)) ^ 2 ∧
      (inner ℝ v w / (‖v‖ * ‖w‖)) ^ 2 < 1) :
    0 < angle v w ∧ angle v w < Real.pi / 12 := by
  have hv : v ≠ 0 := by intro h; simp [h] at hip
  have hw : w ≠ 0 := by intro h; simp [h] at hip
  let c : ℝ := inner ℝ v w / (‖v‖ * ‖w‖)
  have hc : 0 < c := div_pos hip (mul_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hw))
  have hclt : c < 1 := by dsimp [c] at *; nlinarith [hSq.2]
  have hroot : Real.cos (Real.pi / 12) < c := by
    have hbound := cos_pi_div_twelve_sq_lt
    dsimp [c] at *
    nlinarith [hSq.1]
  change 0 < Real.arccos c ∧ Real.arccos c < Real.pi / 12
  refine ⟨Real.arccos_pos.mpr hclt, ?_⟩
  have h := Real.arccos_lt_arccos (Real.neg_one_le_cos _) hroot hclt.le
  rw [Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])] at h
  exact h

/-- The existing least-prime denominator margin implies the slope margin
needed below; no primality assumption is needed once its strict bound is known. -/
theorem denominator_slope_lt_eighth (d J p N : ℝ) (hd : 3 ≤ d)
    (hJ : 0 ≤ J) (hp : 0 ≤ p) (hN : 0 < N)
    (hden : 32 * d * J * p < N) :
    0 ≤ J * p / N ∧ J * p / N < 1 / 8 := by
  constructor
  · positivity
  · apply (div_lt_iff₀ hN).mpr
    have hjp : 0 ≤ J * p := mul_nonneg hJ hp
    have hm := mul_nonneg (sub_nonneg.mpr hd) hjp
    nlinarith

/-- Exact numerical parameters of the supplied four-dimensional 56-site
recipe. This is an arithmetic fact, not a keyed-body identification. -/
theorem recipe_4357_slope_lt_eighth :
    0 < (2 : ℝ) * 17 / 4357 ∧ (2 : ℝ) * 17 / 4357 < 1 / 8 := by
  norm_num

end
end SpectreGeometry.KeyNormalTwelfthAngle
