module

public import ProductClosure.NativeAngleSeparation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

@[expose] public section

/-!
# Actual native normal-angle bounds and prime label separation

The angles are Mathlib's ordinary unoriented Euclidean angles of the proved
native affine normals. Their strict `(0, pi/4)` bounds and label separation
are derived from the chosen prime denominator and actual coefficient bounds.
Material-angle summation for a tiling is a separate obligation.
-/

namespace ProductClosure.NativeCompiler
open PhysicalRegistration
open scoped InnerProductSpace
open InnerProductGeometry
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

theorem native_sideSlope_sq_bounds {J : ℕ} (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m) :
    0 < sideSlope a u s ^ 2 ∧ sideSlope a u s ^ 2 < 1 / 4 := by
  have hnum := slopeNumerator_bounds a u s
  have hp : sidePrime J s ≤ pMax m J :=
    (keyPrime_strictMono J).monotone (by
      have := sidePrime_index_lt s
      omega)
  have hb : slopeNumerator a u s ≤ J * pMax m J :=
    Nat.mul_le_mul (coefficient_natAbs_bounds a u).2 hp
  have hN : 0 < (denominator m J : ℝ) := by exact_mod_cast (denominator_prime m J).pos
  have hrpos : 0 < (slopeNumerator a u s : ℝ) / denominator m J :=
    div_pos (by exact_mod_cast hnum.1) hN
  have hrle : (slopeNumerator a u s : ℝ) / denominator m J ≤
      (J : ℝ) * pMax m J / denominator m J :=
    div_le_div_of_nonneg_right (by exact_mod_cast hb) hN.le
  have hrlt := hrle.trans_lt (native_slope_lt_half m J hm).2
  rw [sideSlope_sq]
  constructor <;> nlinarith

theorem base_normalCosSq_bounds {J : ℕ} (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m) :
    1 / 2 < normalCosSq (sideNormal a u s) (outward u.1) ∧
      normalCosSq (sideNormal a u s) (outward u.1) < 1 := by
  rw [base_normalCosSq]
  have hs := native_sideSlope_sq_bounds hm a u s
  have hd : 0 < 1 + sideSlope a u s ^ 2 := by positivity
  constructor
  · apply (lt_div_iff₀ hd).mpr
    nlinarith
  · apply (div_lt_iff₀ hd).mpr
    nlinarith

theorem side_normalCosSq_bounds {J : ℕ} (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1) :
    1 / 2 < normalCosSq (sideNormal a u s) (sideNormal a u t) ∧
      normalCosSq (sideNormal a u s) (sideNormal a u t) < 1 := by
  rw [side_normalCosSq a u s t hst]
  have hs := native_sideSlope_sq_bounds hm a u s
  have ht := native_sideSlope_sq_bounds hm a u t
  have hd : 0 < (1 + sideSlope a u s ^ 2) * (1 + sideSlope a u t ^ 2) := by positivity
  have hprod : sideSlope a u s ^ 2 * sideSlope a u t ^ 2 < 1 / 16 := by
    nlinarith [mul_pos hs.1 ht.1, mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr ht.2)]
  constructor
  · apply (lt_div_iff₀ hd).mpr
    nlinarith
  · apply (div_lt_iff₀ hd).mpr
    nlinarith [mul_pos hs.1 ht.1]

theorem cos_angle_sq_eq_normalCosSq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v w : E) :
    Real.cos (angle v w) ^ 2 = normalCosSq v w := by
  rw [cos_angle]
  simp [normalCosSq, div_pow, mul_pow]

private theorem angle_bounds_of_normalCosSq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v w : E)
    (hip : 0 < ⟪v, w⟫_ℝ)
    (hSq : 1 / 2 < normalCosSq v w ∧ normalCosSq v w < 1) :
    0 < angle v w ∧ angle v w < Real.pi / 4 := by
  have hv : v ≠ 0 := by intro h; simp [h] at hip
  have hw : w ≠ 0 := by intro h; simp [h] at hip
  let c : ℝ := ⟪v, w⟫_ℝ / (‖v‖ * ‖w‖)
  have hc : 0 < c := div_pos hip (mul_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hw))
  have hcsq : c ^ 2 = normalCosSq v w := by
    dsimp [c]
    simp [normalCosSq, div_pow, mul_pow]
  have hclt : c < 1 := by nlinarith [hSq.2, hcsq]
  have hroot : Real.sqrt 2 / 2 < c := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hp := Real.sqrt_nonneg (2 : ℝ)
    nlinarith [hSq.1, hcsq]
  change 0 < Real.arccos c ∧ Real.arccos c < Real.pi / 4
  refine ⟨Real.arccos_pos.mpr hclt, ?_⟩
  have h := Real.arccos_lt_arccos (by nlinarith [Real.sqrt_nonneg (2 : ℝ)] : (-1 : ℝ) ≤ Real.sqrt 2 / 2) hroot hclt.le
  rw [← Real.cos_pi_div_four, Real.arccos_cos (by positivity)
    (by linarith [Real.pi_pos])] at h
  exact h

/-- Every actual base deviation is nonzero and strictly smaller than pi/4. -/
theorem base_normal_angle_bounds {J : ℕ} (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m) :
    0 < angle (sideNormal a u s) (outward u.1) ∧
      angle (sideNormal a u s) (outward u.1) < Real.pi / 4 :=
  angle_bounds_of_normalCosSq _ _ (by rw [sideNormal_inner_outward]; norm_num)
    (base_normalCosSq_bounds hm a u s)

/-- Every actual distinct-axis side-side deviation has the same strict bound. -/
theorem side_normal_angle_bounds {J : ℕ} (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1) :
    0 < angle (sideNormal a u s) (sideNormal a u t) ∧
      angle (sideNormal a u s) (sideNormal a u t) < Real.pi / 4 :=
  angle_bounds_of_normalCosSq _ _
    (by rw [sideNormal_inner_of_distinct_axes a u s t hst]; norm_num)
    (side_normalCosSq_bounds hm a u s t hst)

/-- Equality of actual base angles identifies the positive magnitude and side label. -/
theorem base_normal_angle_injective {J : ℕ} (a b : Coefficients polyCells J)
    (u v : Site polyCells) (s t : Side m)
    (h : angle (sideNormal a u s) (outward u.1) =
      angle (sideNormal b v t) (outward v.1)) :
    |a.value u| = |b.value v| ∧ s = t := by
  apply base_normalCosSq_injective a b u v s t
  rw [← cos_angle_sq_eq_normalCosSq, ← cos_angle_sq_eq_normalCosSq, h]

/-- An actual base angle never equals a distinct-axis side-side angle. -/
theorem base_normal_angle_ne_side_normal_angle {J : ℕ} (a b : Coefficients polyCells J)
    (u v : Site polyCells) (s t r : Side m) (htr : t.1 ≠ r.1) :
    angle (sideNormal a u s) (outward u.1) ≠
      angle (sideNormal b v t) (sideNormal b v r) := by
  intro h
  apply base_normalCosSq_ne_side_normalCosSq a b u v s t r htr
  rw [← cos_angle_sq_eq_normalCosSq, ← cos_angle_sq_eq_normalCosSq, h]

theorem angle_placedNormal  (f : Space m ≃ᵢ Space m) (v w : Space m) :
    angle (placedNormal f v) (placedNormal f w) = angle v w := by
  exact f.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearIsometry.angle_map v w

theorem placed_base_normal_angle_bounds {J : ℕ} (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m) (f : Space m ≃ᵢ Space m) :
    0 < angle (placedNormal f (sideNormal a u s)) (placedNormal f (outward u.1)) ∧
      angle (placedNormal f (sideNormal a u s)) (placedNormal f (outward u.1)) < Real.pi / 4 := by
  rw [angle_placedNormal]
  exact base_normal_angle_bounds hm a u s

theorem placed_side_normal_angle_bounds {J : ℕ} (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1)
    (f : Space m ≃ᵢ Space m) :
    0 < angle (placedNormal f (sideNormal a u s)) (placedNormal f (sideNormal a u t)) ∧
      angle (placedNormal f (sideNormal a u s)) (placedNormal f (sideNormal a u t)) < Real.pi / 4 := by
  rw [angle_placedNormal]
  exact side_normal_angle_bounds hm a u s t hst

theorem placed_base_normal_angle_injective {J : ℕ} (a b : Coefficients polyCells J)
    (u v : Site polyCells) (s t : Side m) (f g : Space m ≃ᵢ Space m)
    (h : angle (placedNormal f (sideNormal a u s)) (placedNormal f (outward u.1)) =
      angle (placedNormal g (sideNormal b v t)) (placedNormal g (outward v.1))) :
    |a.value u| = |b.value v| ∧ s = t := by
  rw [angle_placedNormal, angle_placedNormal] at h
  exact base_normal_angle_injective a b u v s t h

theorem placed_base_normal_angle_ne_side_normal_angle {J : ℕ} (a b : Coefficients polyCells J)
    (u v : Site polyCells) (s t r : Side m) (htr : t.1 ≠ r.1) (f g : Space m ≃ᵢ Space m) :
    angle (placedNormal f (sideNormal a u s)) (placedNormal f (outward u.1)) ≠
      angle (placedNormal g (sideNormal b v t)) (placedNormal g (sideNormal b v r)) := by
  rw [angle_placedNormal, angle_placedNormal]
  exact base_normal_angle_ne_side_normal_angle a b u v s t r htr

end
end ProductClosure.NativeCompiler
