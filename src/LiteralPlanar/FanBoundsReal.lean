module

public import LiteralPlanar.FanBoundsData
public import LiteralPlanar.QuinticFanLipschitz
public import SpectreGeometry.PolygonReal

@[expose] public section


/-! Real-coordinate interpretation of the exact fan-margin certificates.
No physical tiling, disk or global Lipschitz conclusion is asserted here. -/
namespace LiteralPlanar.FanBounds
noncomputable section
open SpectreGeometry

def center : RealPoint := realize fanCenter

def radial (i : Fin 14) : RealPoint := realVertex i - center

def areaDeterminant (i : Fin 14) : ℝ :=
  RealPoint.det (radial i) (radial (next i))

theorem radial_squared_lt_nine (i : Fin 14) :
    RealPoint.dot (radial i) (radial i) < 9 := by
  have h := Quad3.positive_sound _ (center_radius_squared_lt_nine i)
  rw [Quad3.eval_sub] at h
  have he := realize_dot (ExactPoint.sub (vertex i) fanCenter)
    (ExactPoint.sub (vertex i) fanCenter)
  rw [realize_sub] at he
  change RealPoint.dot (radial i) (radial i) = _ at he
  norm_num only [Quad3.eval, Int.cast_ofNat, Int.cast_zero, zero_mul, add_zero] at h he
  linarith

theorem areaDeterminant_gt_tenth (i : Fin 14) :
    (1 / 10 : ℝ) < areaDeterminant i := by
  have h := Quad3.positive_sound _ (fan_determinant_gt_tenth i)
  rw [Quad3.eval_sub, Quad3.eval_mul] at h
  have he := realize_det (edge i) (ExactPoint.sub fanCenter (vertex i))
  rw [realize_edge, realize_sub] at he
  have hd : RealPoint.det (realEdge i) (RealPoint.sub (realize fanCenter) (realize (vertex i))) =
      areaDeterminant i := by
    simp only [areaDeterminant, radial, center, realVertex, realEdge,
      RealPoint.det, RealPoint.sub, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [hd] at he
  norm_num only [Quad3.eval, Int.cast_ofNat, Int.cast_zero, zero_mul, add_zero] at h he
  linarith

theorem areaDeterminant_pos (i : Fin 14) : 0 < areaDeterminant i :=
  lt_trans (by norm_num) (areaDeterminant_gt_tenth i)

def alpha (i : Fin 14) (p : RealPoint) : ℝ :=
  RealPoint.det (p - center) (radial (next i)) / areaDeterminant i

def beta (i : Fin 14) (p : RealPoint) : ℝ :=
  RealPoint.det (radial i) (p - center) / areaDeterminant i

/-- Ordinary Euclidean Lagrange identity, expressed in the project's coordinates. -/
theorem det_squared_le (u v : RealPoint) :
    RealPoint.det u v ^ 2 ≤ RealPoint.dot u u * RealPoint.dot v v := by
  have he : RealPoint.det u v ^ 2 + RealPoint.dot u v ^ 2 =
      RealPoint.dot u u * RealPoint.dot v v := by
    simp only [RealPoint.det, RealPoint.dot]
    ring
  nlinarith [sq_nonneg (RealPoint.dot u v)]

/-- A useful norm-free interface: r is any nonnegative Euclidean length of w. -/
theorem abs_radial_det_bound (i : Fin 14) (w : RealPoint) (r : ℝ)
    (hr : 0 ≤ r) (hw : RealPoint.dot w w = r ^ 2) :
    |RealPoint.det w (radial i)| ≤ 3 * r := by
  have hd := det_squared_le w (radial i)
  rw [hw] at hd
  have hb := mul_le_mul_of_nonneg_left (radial_squared_lt_nine i).le (sq_nonneg r)
  apply (sq_le_sq₀ (abs_nonneg _) (by linarith : 0 ≤ 3 * r)).mp
  rw [sq_abs]
  nlinarith

theorem alpha_difference_bound (i : Fin 14) (p q : RealPoint) (r : ℝ)
    (hr : 0 ≤ r) (hpq : RealPoint.dot (p - q) (p - q) = r ^ 2) :
    |alpha i p - alpha i q| ≤ 30 * r := by
  have hd := areaDeterminant_pos i
  have he : alpha i p - alpha i q =
      RealPoint.det (p - q) (radial (next i)) / areaDeterminant i := by
    simp only [alpha, RealPoint.det, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [he, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hb := abs_radial_det_bound (next i) (p - q) r hr hpq
  have hmargin := areaDeterminant_gt_tenth i
  have hm := mul_nonneg hr (le_of_lt (sub_pos.mpr hmargin))
  nlinarith

theorem beta_difference_bound (i : Fin 14) (p q : RealPoint) (r : ℝ)
    (hr : 0 ≤ r) (hpq : RealPoint.dot (p - q) (p - q) = r ^ 2) :
    |beta i p - beta i q| ≤ 30 * r := by
  have hd := areaDeterminant_pos i
  have he : beta i p - beta i q =
      -(RealPoint.det (p - q) (radial i)) / areaDeterminant i := by
    simp only [beta, RealPoint.det, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [he, abs_div, abs_neg, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hb := abs_radial_det_bound i (p - q) r hr hpq
  have hmargin := areaDeterminant_gt_tenth i
  have hm := mul_nonneg hr (le_of_lt (sub_pos.mpr hmargin))
  nlinarith

def sourceDomain (i : Fin 14) : Set RealPoint :=
  {p | 0 ≤ alpha i p ∧ 0 ≤ beta i p ∧ alpha i p + beta i p ≤ 1}

/-- Quantitative displacement control on the literal barycentric simplex.
The length parameter is the Euclidean one, specified by its squared norm. -/
theorem fan_displacement_scalar_bound (i : Fin 14) (p q : RealPoint) (r : ℝ)
    (hp : p ∈ sourceDomain i) (hq : q ∈ sourceDomain i)
    (hr : 0 ≤ r) (hpq : RealPoint.dot (p - q) (p - q) = r ^ 2) :
    |Quintic.fanHeight Quintic.amplitude (alpha i p) (beta i p) -
      Quintic.fanHeight Quintic.amplitude (alpha i q) (beta i q)| ≤
        90 * Quintic.amplitude * r := by
  obtain ⟨hpa, hpb, hps⟩ := hp
  obtain ⟨hqa, hqb, hqs⟩ := hq
  exact Quintic.fanHeight_difference_bound_of_parameter_bounds
    Quintic.amplitude (alpha i p) (beta i p) (alpha i q) (beta i q) r
    Quintic.amplitude_pos.le ⟨hpa, by linarith⟩ ⟨hpb, by linarith⟩
    ⟨hqa, by linarith⟩ ⟨hqb, by linarith⟩
    (alpha_difference_bound i p q r hr hpq) (beta_difference_bound i p q r hr hpq)

end
end LiteralPlanar.FanBounds
