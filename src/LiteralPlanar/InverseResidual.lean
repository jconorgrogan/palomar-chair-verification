module

public import SpectreGeometry.DeformationHomeomorphism
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! A small forward displacement gives a small inverse displacement. This
quantitative lemma supplies a strict contraction for reverse physical pasting;
it does not itself assume or assert any tiling-decoding compatibility. -/
namespace LiteralPlanar
noncomputable section
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E]

theorem inverse_lipschitz_of_small_residual (H : E ≃ₜ E) (g : E → E)
    (hH : ∀ x, H x = x+g x) (hg : LipschitzWith (1/8 : ℝ≥0) g) :
    LipschitzWith 2 H.symm := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  let u := H.symm y
  let v := H.symm z
  have hnorm := norm_sub_le (H u-H v) (g u-g v)
  have he : (H u-H v)-(g u-g v)=u-v := by rw [hH,hH]; abel
  rw [he,←dist_eq_norm,←dist_eq_norm,←dist_eq_norm] at hnorm
  have hsmall := hg.dist_le_mul u v
  have hy : H u = y := H.apply_symm_apply y
  have hz : H v = z := H.apply_symm_apply z
  rw [hy,hz] at hnorm
  norm_num at hsmall ⊢
  change dist u v ≤ 2*dist y z
  nlinarith [dist_nonneg (x:=y) (y:=z)]

theorem inverse_residual_lipschitz (H : E ≃ₜ E) (g : E → E)
    (hH : ∀ x, H x = x+g x) (hg : LipschitzWith (1/8 : ℝ≥0) g) :
    LipschitzWith (1/4 : ℝ≥0) (fun y => H.symm y-y) := by
  have hi := inverse_lipschitz_of_small_residual H g hH hg
  have hid (y : E) : H.symm y-y = -g (H.symm y) := by
    have hh := hH (H.symm y)
    rw [H.apply_symm_apply] at hh
    conv_lhs => rhs; rw [hh]
    abel
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [hid,hid,dist_neg_neg]
  have hh := hg.dist_le_mul (H.symm y) (H.symm z)
  have hii := hi.dist_le_mul y z
  norm_num at hh hii ⊢
  nlinarith

end
end LiteralPlanar
