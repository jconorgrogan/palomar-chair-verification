module

public import LiteralPlanar.CurvedInverseMaps
public import LiteralPlanar.InverseResidual

@[expose] public section


/-! Uniform small inverse displacement for each arbitrary physical placement.
The bound is derived by isometric conjugation from the genuine whole-plane
forward homeomorphism, not assumed on the physical tiling. -/
namespace LiteralPlanar
noncomputable section
open scoped NNReal
open SpectreGeometry

theorem isometry_difference_linear (A : EPlane ≃ᵢ EPlane) (x y : EPlane) :
    A x-A y = A.toRealLinearIsometryEquiv (x-y) := by
  rw [map_sub,IsometryEquiv.toRealLinearIsometryEquiv_apply,
    IsometryEquiv.toRealLinearIsometryEquiv_apply]
  abel

theorem conjugate_residual_lipschitz (A : EPlane ≃ᵢ EPlane) (H : EPlane ≃ₜ EPlane)
    (c : ℝ≥0) (hc : LipschitzWith c (fun x => H x-x)) :
    LipschitzWith c (fun x => A.symm (H (A x))-x) := by
  have he (x : EPlane) : A.symm (H (A x))-x =
      A.symm.toRealLinearIsometryEquiv (H (A x)-A x) := by
    rw [←isometry_difference_linear,IsometryEquiv.symm_apply_apply]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [he,he,A.symm.toRealLinearIsometryEquiv.dist_map]
  simpa only [A.dist_eq] using hc.dist_le_mul (A x) (A y)

namespace Forward
open Candidate FanBounds
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p) (root : I)

theorem tileHomeomorph_residual_lipschitz :
    LipschitzWith (1/8 : ℝ≥0) (fun x => tileHomeomorph p T root x-x) := by
  have hg : LipschitzWith (1/8 : ℝ≥0) (fun x => curvedHomeomorph p T x-x) := by
    simp only [curvedHomeomorph_apply,add_sub_cancel_left]
    exact (globalResidual_lipschitz p T).weaken (by apply NNReal.coe_le_coe.mp; norm_num)
  exact conjugate_residual_lipschitz (p root) (curvedHomeomorph p T) (1/8) hg

theorem tileHomeomorph_inverse_residual_lipschitz :
    LipschitzWith (1/4 : ℝ≥0) (fun x => (tileHomeomorph p T root).symm x-x) := by
  apply inverse_residual_lipschitz (tileHomeomorph p T root)
    (fun x => tileHomeomorph p T root x-x)
  · intro x
    abel
  · exact tileHomeomorph_residual_lipschitz p T root

theorem placedInverse_residual_lipschitz (f : EPlane ≃ᵢ EPlane) :
    LipschitzWith (1/4 : ℝ≥0) (fun x => placedInverse p T root f x-x) := by
  have h := conjugate_residual_lipschitz f.symm (tileHomeomorph p T root).symm (1/4)
    (tileHomeomorph_inverse_residual_lipschitz p T root)
  simpa only [IsometryEquiv.symm_symm,placedInverse] using h

end Forward
end
end LiteralPlanar
