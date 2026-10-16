module

public import LiteralPlanar.FanBoundsReal
public import SpectreGeometry.FanRealGeometry

@[expose] public section


/-! The quantitative displacement estimate applies to the exact original
fan triangles, not to an unrelated coordinate simplex. -/
namespace LiteralPlanar.FanBounds
noncomputable section
open SpectreGeometry

private theorem alpha_area (i : Fin 14) (p : RealPoint) :
    areaDeterminant i * alpha i p = RealPoint.det (p - center) (radial (next i)) := by
  rw [mul_comm, alpha, div_mul_cancel₀ _ (areaDeterminant_pos i).ne']

private theorem beta_area (i : Fin 14) (p : RealPoint) :
    areaDeterminant i * beta i p = RealPoint.det (radial i) (p - center) := by
  rw [mul_comm, beta, div_mul_cancel₀ _ (areaDeterminant_pos i).ne']

theorem radialSide_beta (i : Fin 14) (p : RealPoint) :
    radialSide i p = areaDeterminant i * beta i p := by
  rw [beta_area]
  rfl

theorem radialSide_next_alpha (i : Fin 14) (p : RealPoint) :
    radialSide (next i) p = -(areaDeterminant i * alpha i p) := by
  rw [alpha_area]
  simp only [radialSide, side, radial, center, realFanCenter,
    RealPoint.det, RealPoint.sub, Prod.fst_sub, Prod.snd_sub]
  ring

theorem outerSide_barycentric (i : Fin 14) (p : RealPoint) :
    side (realVertex i) (realVertex (next i)) p =
      areaDeterminant i * (1 - alpha i p - beta i p) := by
  rw [mul_sub, mul_sub, mul_one, alpha_area, beta_area]
  simp only [side, areaDeterminant, radial, center,
    RealPoint.det, RealPoint.sub, Prod.fst_sub, Prod.snd_sub]
  ring

/-- The domain in the genuine Euclidean Lipschitz theorem is the original
closed fan triangle in barycentric coordinates. -/
theorem sourceDomain_eq_triangleBody (i : Fin 14) : sourceDomain i = triangleBody i := by
  ext p
  rw [triangleBody_mem_iff, radialSide_beta, radialSide_next_alpha, outerSide_barycentric]
  have hd := areaDeterminant_pos i
  simp only [sourceDomain, Set.mem_setOf_eq,
    mul_nonneg_iff_of_pos_left hd, neg_nonpos]
  constructor
  · rintro ⟨ha,hb,hs⟩
    exact ⟨hb, by linarith, ha⟩
  · rintro ⟨hb,hs,ha⟩
    exact ⟨ha,hb, by linarith⟩

/-- The quantitative scalar estimate applies on the exact original triangle. -/
theorem fan_displacement_bound_on_triangle (i : Fin 14) (p q : RealPoint) (r : ℝ)
    (hp : p ∈ triangleBody i) (hq : q ∈ triangleBody i)
    (hr : 0 ≤ r) (hpq : RealPoint.dot (p - q) (p - q) = r ^ 2) :
    |Quintic.fanHeight Quintic.amplitude (alpha i p) (beta i p) -
      Quintic.fanHeight Quintic.amplitude (alpha i q) (beta i q)| ≤
        90 * Quintic.amplitude * r := by
  apply fan_displacement_scalar_bound i p q r
  · rwa [sourceDomain_eq_triangleBody]
  · rwa [sourceDomain_eq_triangleBody]
  · exact hr
  · exact hpq

end
end LiteralPlanar.FanBounds
