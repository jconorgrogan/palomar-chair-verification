module

public import SparseMonotiles.SectorAngleSumHalfplanes
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Actual two-half-plane wedge traces -/

namespace SparseMonotiles
namespace SectorAngleSum

open Set Metric InnerProductGeometry
open scoped InnerProductSpace

@[simp] theorem direction_zero : direction 0 = 1 := by
  change ((Real.Angle.toCircle 0 : Circle) : ℂ) = 1
  rw [Real.Angle.toCircle_zero, Circle.coe_one]

@[simp] theorem direction_coe_re (a : ℝ) : (direction (a : AddCircle (2 * Real.pi))).re = Real.cos a := by
  change (Complex.exp (a * Complex.I)).re = Real.cos a
  simp [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

@[simp] theorem direction_coe_im (a : ℝ) : (direction (a : AddCircle (2 * Real.pi))).im = Real.sin a := by
  change (Complex.exp (a * Complex.I)).im = Real.sin a
  simp [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- A radial cosine cap is exactly the corresponding circular arc. -/
theorem cosine_cap_trace (b : ℝ) (hb0 : 0 ≤ b) (hbπ : b ≤ Real.pi) :
    {q : AddCircle (2 * Real.pi) | Real.cos b ≤ (direction q).re} =
      closedArc 0 (2 * b) := by
  ext q
  change Real.cos b ≤ (direction q).re ↔ dist q 0 ≤ (2 * b) / 2
  rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0), ← angle_direction_eq_dist,
    direction_zero, angle, norm_direction, norm_one, one_mul, div_one, Complex.inner]
  simp only [one_mul, Complex.conj_re]
  have hlo : -1 ≤ (direction q).re := by
    exact (abs_le.mp (show |(direction q).re| ≤ 1 by
      simpa only [norm_direction] using Complex.abs_re_le_norm (direction q))).1
  have hhi : (direction q).re ≤ 1 := by
    simpa only [norm_direction] using Complex.re_le_norm (direction q)
  constructor
  · intro h
    simpa only [Real.arccos_cos hb0 hbπ] using Real.arccos_le_arccos h
  · intro h
    have hm := Real.cos_le_cos_of_nonneg_of_le_pi
      (Real.arccos_nonneg (direction q).re) hbπ h
    rwa [Real.cos_arccos hlo hhi] at hm

private theorem symmetric_linear_inequalities {c s x y : ℝ}
    (hc : 0 < c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hxy : x ^ 2 + y ^ 2 = 1) :
    (0 ≤ c * x + s * y ∧ 0 ≤ c * x - s * y) ↔ s ≤ x := by
  have hid : (c*x)^2 - (s*y)^2 = x^2 - s^2 := by
    linear_combination x^2 * hcs - s^2 * hxy
  constructor
  · rintro ⟨h₁,h₂⟩
    have hcx : 0 ≤ c*x := by linarith
    have hx : 0 ≤ x := (mul_nonneg_iff_of_pos_left hc).mp hcx
    have hprod := mul_nonneg h₁ h₂
    nlinarith
  · intro hx
    have hcx : 0 ≤ c*x := mul_nonneg hc.le (hs.trans hx)
    have hsq : (s*y)^2 ≤ (c*x)^2 := by nlinarith
    have ha : |s*y| ≤ c*x := (sq_le_sq₀ (abs_nonneg _) hcx).mp (by simpa only [sq_abs] using hsq)
    exact ⟨by linarith [(abs_le.mp ha).1], by linarith [(abs_le.mp ha).2]⟩

private theorem symmetric_strict_linear_inequalities {c s x y : ℝ}
    (hc : 0 < c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hxy : x ^ 2 + y ^ 2 = 1) :
    (0 < c * x + s * y ∧ 0 < c * x - s * y) ↔ s < x := by
  have hid : (c*x)^2 - (s*y)^2 = x^2 - s^2 := by
    linear_combination x^2 * hcs - s^2 * hxy
  constructor
  · rintro ⟨h₁,h₂⟩
    have hcx : 0 < c*x := by linarith
    have hx : 0 < x := (mul_pos_iff_of_pos_left hc).mp hcx
    have hprod := mul_pos h₁ h₂
    nlinarith
  · intro hx
    have hcx : 0 ≤ c*x := mul_nonneg hc.le (hs.trans hx.le)
    have hsq : (s*y)^2 < (c*x)^2 := by nlinarith
    have ha : |s*y| < c*x := (sq_lt_sq₀ (abs_nonneg _) hcx).mp (by simpa only [sq_abs] using hsq)
    exact ⟨by linarith [(abs_lt.mp ha).1], by linarith [(abs_lt.mp ha).2]⟩

/-- Two symmetric inward normals separated by `2a < π` cut out the genuine
closed convex wedge of angle `π-2a`. -/
theorem symmetric_halfplanes_inter_trace (a : ℝ) (ha0 : 0 ≤ a) (haπ : a < Real.pi / 2) :
    closedArc (a : AddCircle (2 * Real.pi)) Real.pi ∩
      closedArc (-a : AddCircle (2 * Real.pi)) Real.pi =
        closedArc 0 (Real.pi - 2*a) := by
  rw [← halfplane_unit_trace, ← halfplane_unit_trace]
  have hwidth : Real.pi - 2*a = 2 * (Real.pi/2-a) := by ring
  rw [hwidth, ← cosine_cap_trace _ (by linarith) (by linarith [Real.pi_pos])]
  ext q
  simp only [mem_inter_iff, mem_setOf_eq, Complex.inner, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, ← AddCircle.coe_neg, direction_coe_re, direction_coe_im,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two_sub]
  have hc := Real.cos_pos_of_mem_Ioo (show a ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith [Real.pi_pos], haπ⟩)
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ha0 (by linarith : a ≤ Real.pi)
  have hxy : (direction q).re ^ 2 + (direction q).im ^ 2 = 1 := by
    have hn := norm_direction q
    have hs := Complex.normSq_eq_norm_sq (direction q)
    rw [hn, one_pow, Complex.normSq_apply] at hs
    nlinarith [hs]
  convert symmetric_linear_inequalities hc hs (Real.cos_sq_add_sin_sq a) hxy using 1 <;> ring_nf

private theorem symmetric_union_linear_inequalities {c s x y : ℝ}
    (hc : 0 < c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hxy : x ^ 2 + y ^ 2 = 1) :
    (0 ≤ c * x + s * y ∨ 0 ≤ c * x - s * y) ↔ -s ≤ x := by
  have hh := symmetric_strict_linear_inequalities (x := -x) (y := -y) hc hs hcs
    (by nlinarith : (-x)^2 + (-y)^2 = 1)
  constructor
  · intro h
    by_contra hn
    have hx : s < -x := by linarith
    obtain ⟨h₁,h₂⟩ := hh.mpr hx
    rcases h with h | h <;> nlinarith
  · intro hx
    by_contra hn
    push_neg at hn
    have ha : s < -x := hh.mp ⟨by nlinarith [hn.1], by nlinarith [hn.2]⟩
    linarith

/-- The union of the same inward half-planes is the genuine reflex wedge,
whose angle is `π+2a`. -/
theorem symmetric_halfplanes_union_trace (a : ℝ) (ha0 : 0 ≤ a) (haπ : a < Real.pi / 2) :
    closedArc (a : AddCircle (2 * Real.pi)) Real.pi ∪
      closedArc (-a : AddCircle (2 * Real.pi)) Real.pi =
        closedArc 0 (Real.pi + 2*a) := by
  rw [← halfplane_unit_trace, ← halfplane_unit_trace]
  have hwidth : Real.pi + 2*a = 2 * (Real.pi/2+a) := by ring
  rw [hwidth, ← cosine_cap_trace _ (by linarith [Real.pi_pos]) (by linarith)]
  ext q
  simp only [mem_union, mem_setOf_eq, Complex.inner, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, ← AddCircle.coe_neg, direction_coe_re, direction_coe_im,
    Real.cos_neg, Real.sin_neg, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_sub]
  have hc := Real.cos_pos_of_mem_Ioo (show a ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith [Real.pi_pos], haπ⟩)
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ha0 (by linarith : a ≤ Real.pi)
  have hxy : (direction q).re ^ 2 + (direction q).im ^ 2 = 1 := by
    have hn := norm_direction q
    have hs := Complex.normSq_eq_norm_sq (direction q)
    rw [hn, one_pow, Complex.normSq_apply] at hs
    nlinarith [hs]
  convert symmetric_union_linear_inequalities hc hs (Real.cos_sq_add_sin_sq a) hxy using 1 <;> ring_nf

/-- Translation of an angular arc is an exact isometry. -/
theorem mem_closedArc_add_center (q c a : AddCircle (2 * Real.pi)) (θ : ℝ) :
    q ∈ closedArc (c+a) θ ↔ q-c ∈ closedArc a θ := by
  simp only [closedArc, mem_closedBall, dist_eq_norm]
  congr 2
  abel

/-- The symmetric wedge identity holds about every angular midpoint. -/
theorem halfplanes_inter_trace_of_midpoint (c : AddCircle (2 * Real.pi))
    (a : ℝ) (ha0 : 0 ≤ a) (haπ : a < Real.pi/2) :
    closedArc (c+(a : AddCircle (2*Real.pi))) Real.pi ∩
      closedArc (c-(a : AddCircle (2*Real.pi))) Real.pi =
        closedArc c (Real.pi-2*a) := by
  ext q
  have h := Set.ext_iff.mp (symmetric_halfplanes_inter_trace a ha0 haπ) (q-c)
  have ht := mem_closedArc_add_center q c 0 (Real.pi-2*a)
  simp only [add_zero] at ht
  rw [ht]
  simpa only [mem_inter_iff, mem_closedArc_add_center, sub_eq_add_neg] using h

/-- The reflex wedge identity holds about every angular midpoint. -/
theorem halfplanes_union_trace_of_midpoint (c : AddCircle (2 * Real.pi))
    (a : ℝ) (ha0 : 0 ≤ a) (haπ : a < Real.pi/2) :
    closedArc (c+(a : AddCircle (2*Real.pi))) Real.pi ∪
      closedArc (c-(a : AddCircle (2*Real.pi))) Real.pi =
        closedArc c (Real.pi+2*a) := by
  ext q
  have h := Set.ext_iff.mp (symmetric_halfplanes_union_trace a ha0 haπ) (q-c)
  have ht := mem_closedArc_add_center q c 0 (Real.pi+2*a)
  simp only [add_zero] at ht
  rw [ht]
  simpa only [mem_union, mem_closedArc_add_center, sub_eq_add_neg] using h

#print axioms symmetric_halfplanes_inter_trace
#print axioms symmetric_halfplanes_union_trace

end SectorAngleSum
end SparseMonotiles
