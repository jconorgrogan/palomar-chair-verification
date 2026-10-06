module

public import SparseMonotiles.SectorAngleSumWedges

@[expose] public section

/-! # Geometric widths of arbitrary non-antipodal two-normal wedges -/

namespace SparseMonotiles
namespace SectorAngleSum

open Set Metric InnerProductGeometry
open scoped InnerProductSpace

/-- Any two non-antipodal directions have a midpoint and opposite signed half
separations. This uses their actual circular distance, not a supplied angle. -/
theorem exists_angular_midpoint (c d : AddCircle (2 * Real.pi))
    (hcd : dist c d < Real.pi) :
    ∃ (m : AddCircle (2 * Real.pi)) (a : ℝ),
      0 ≤ a ∧ a < Real.pi/2 ∧ 2*a = dist c d ∧
      ((c = m+(a : AddCircle (2*Real.pi)) ∧ d = m-(a : AddCircle (2*Real.pi))) ∨
       (c = m-(a : AddCircle (2*Real.pi)) ∧ d = m+(a : AddCircle (2*Real.pi)))) := by
  let r : ℝ := Complex.arg (direction (c-d))
  have hr : (r : AddCircle (2 * Real.pi)) = c-d := Real.Angle.arg_toCircle _
  have hrnorm : ‖(r : AddCircle (2 * Real.pi))‖ = |r| := by
    apply (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity)).mpr
    simpa only [abs_of_pos Real.two_pi_pos, mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)]
      using Complex.abs_arg_le_pi (direction (c-d))
  have habs : |r| = dist c d := by rw [← hrnorm, hr, dist_eq_norm]
  refine ⟨d+(r/2 : ℝ), |r|/2, by positivity, by rw [habs]; linarith, ?_, ?_⟩
  · rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0), habs]
  · by_cases hr0 : 0 ≤ r
    · left
      rw [abs_of_nonneg hr0]
      constructor
      · rw [add_assoc, ← AddCircle.coe_add, add_halves, hr]
        abel
      · abel
    · right
      have ha : |r|/2 = -(r/2) := by rw [abs_of_neg (lt_of_not_ge hr0)]; ring
      rw [ha, AddCircle.coe_neg]
      constructor
      · rw [sub_neg_eq_add, add_assoc, ← AddCircle.coe_add, add_halves, hr]
        abel
      · abel

/-- Intersection and union widths are determined by the actual separation of
the inward normal directions. Both traces are proved simultaneously. -/
theorem exists_two_semicircle_traces (c d : AddCircle (2 * Real.pi))
    (hcd : dist c d < Real.pi) :
    ∃ m : AddCircle (2 * Real.pi),
      closedArc c Real.pi ∩ closedArc d Real.pi = closedArc m (Real.pi-dist c d) ∧
      closedArc c Real.pi ∪ closedArc d Real.pi = closedArc m (Real.pi+dist c d) := by
  obtain ⟨m,a,ha0,haπ,hd,hpair⟩ := exists_angular_midpoint c d hcd
  refine ⟨m, ?_, ?_⟩
  · rw [← hd]
    rcases hpair with ⟨hc,he⟩ | ⟨hc,he⟩
    · rw [hc,he]; exact halfplanes_inter_trace_of_midpoint m a ha0 haπ
    · rw [hc,he,inter_comm]; exact halfplanes_inter_trace_of_midpoint m a ha0 haπ
  · rw [← hd]
    rcases hpair with ⟨hc,he⟩ | ⟨hc,he⟩
    · rw [hc,he]; exact halfplanes_union_trace_of_midpoint m a ha0 haπ
    · rw [hc,he,union_comm]; exact halfplanes_union_trace_of_midpoint m a ha0 haπ

/-- The argument distance of two nonzero complex normals is exactly their
Euclidean inner-product angle. -/
theorem dist_arg_eq_angle (n m : ℂ) (hn : n ≠ 0) (hm : m ≠ 0) :
    dist (Complex.arg n : AddCircle (2 * Real.pi)) (Complex.arg m) = angle n m := by
  rw [← angle_direction_eq_dist]
  conv_rhs => rw [← norm_smul_direction_arg n, ← norm_smul_direction_arg m]
  rw [angle_smul_left_of_pos _ _ (norm_pos_iff.mpr hn),
    angle_smul_right_of_pos _ _ (norm_pos_iff.mpr hm)]

/-- Actual two-half-space cones have the advertised convex and reflex sector
angles `π-angle(n,m)` and `π+angle(n,m)`. No cone-trace hypothesis remains. -/
theorem two_halfplanes_traces (n m : ℂ) (hn : n ≠ 0) (hm : m ≠ 0)
    (hangle : angle n m < Real.pi) :
    ∃ c : AddCircle (2 * Real.pi),
      {q : AddCircle (2 * Real.pi) |
        0 ≤ ⟪n, direction q⟫_ℝ ∧ 0 ≤ ⟪m, direction q⟫_ℝ} =
          closedArc c (Real.pi-angle n m) ∧
      {q : AddCircle (2 * Real.pi) |
        0 ≤ ⟪n, direction q⟫_ℝ ∨ 0 ≤ ⟪m, direction q⟫_ℝ} =
          closedArc c (Real.pi+angle n m) := by
  obtain ⟨c,hc,hu⟩ := exists_two_semicircle_traces (Complex.arg n) (Complex.arg m)
    (by rwa [dist_arg_eq_angle n m hn hm])
  rw [dist_arg_eq_angle n m hn hm, ← halfplane_trace n hn, ← halfplane_trace m hm] at hc hu
  exact ⟨c,hc,hu⟩

#print axioms exists_angular_midpoint
#print axioms exists_two_semicircle_traces
#print axioms two_halfplanes_traces

end SectorAngleSum
end SparseMonotiles
