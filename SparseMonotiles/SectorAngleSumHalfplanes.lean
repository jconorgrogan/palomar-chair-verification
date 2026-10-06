module

import all Mathlib.Basic.Real.Basic
public import SparseMonotiles.SectorAngleSum
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Complex.Angle

@[expose] public section

/-! # Actual half-plane traces on the radian circle -/

namespace SparseMonotiles
namespace SectorAngleSum

open Set Metric InnerProductGeometry
open scoped InnerProductSpace

/-- The canonical unit direction belonging to a radian angle. -/
noncomputable def direction (q : AddCircle (2 * Real.pi)) : ℂ :=
  (AddCircle.homeomorphCircle' q : ℂ)

@[simp] theorem norm_direction (q : AddCircle (2 * Real.pi)) : ‖direction q‖ = 1 :=
  Circle.norm_coe _

@[simp] theorem direction_ne_zero (q : AddCircle (2 * Real.pi)) : direction q ≠ 0 :=
  Circle.coe_ne_zero _

theorem direction_sub (q c : AddCircle (2 * Real.pi)) :
    direction (q - c) = direction q / direction c := by
  induction q using QuotientAddGroup.induction_on
  induction c using QuotientAddGroup.induction_on
  rw [← AddCircle.coe_sub]
  simp only [direction, AddCircle.homeomorphCircle'_apply_mk]
  rw [sub_eq_add_neg, Circle.exp_add, Circle.exp_neg]
  simp only [Circle.coe_mul, Circle.coe_inv, div_eq_mul_inv]

/-- The quotient-circle metric is exactly the usual Euclidean angle between
its corresponding nonzero unit vectors. -/
theorem angle_direction_eq_dist (q c : AddCircle (2 * Real.pi)) :
    angle (direction q) (direction c) = dist q c := by
  rw [Complex.angle_eq_abs_arg (direction_ne_zero q) (direction_ne_zero c),
    ← direction_sub, dist_eq_norm]
  have ha : ((Complex.arg (direction (q - c)) : ℝ) : AddCircle (2 * Real.pi)) =
      q - c := Real.Angle.arg_toCircle _
  conv_rhs => rw [← ha]
  symm
  apply (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity)).mpr
  simpa only [abs_of_pos Real.two_pi_pos, mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)]
    using Complex.abs_arg_le_pi (direction (q - c))

/-- A half-plane through the origin has precisely the closed semicircular
trace centered on its unit inward normal. -/
theorem halfplane_unit_trace (c : AddCircle (2 * Real.pi)) :
    {q : AddCircle (2 * Real.pi) | 0 ≤ ⟪direction c, direction q⟫_ℝ} =
      closedArc c Real.pi := by
  ext q
  change 0 ≤ ⟪direction c, direction q⟫_ℝ ↔ dist q c ≤ Real.pi / 2
  rw [← angle_direction_eq_dist, angle, norm_direction, norm_direction, one_mul,
    div_one, real_inner_comm]
  exact Real.arccos_le_pi_div_two.symm

/-- A nonzero vector is its positive length times its unit angular direction. -/
theorem norm_smul_direction_arg (n : ℂ) :
    ‖n‖ • direction (Complex.arg n) = n := by
  change (‖n‖ : ℂ) * Complex.exp (Complex.arg n * Complex.I) = n
  exact Complex.norm_mul_exp_arg_mul_I n

/-- Every genuine linear half-plane has a semicircular trace, independent of
the length chosen for its nonzero inward normal. -/
theorem halfplane_trace (n : ℂ) (hn : n ≠ 0) :
    {q : AddCircle (2 * Real.pi) | 0 ≤ ⟪n, direction q⟫_ℝ} =
      closedArc (Complex.arg n) Real.pi := by
  rw [← halfplane_unit_trace]
  ext q
  conv_lhs => rw [← norm_smul_direction_arg n]
  simp only [real_inner_smul_left]
  exact mul_nonneg_iff_of_pos_left (norm_pos_iff.mpr hn)

#print axioms angle_direction_eq_dist
#print axioms halfplane_trace

end SectorAngleSum
end SparseMonotiles
