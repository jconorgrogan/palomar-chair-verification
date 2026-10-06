module

public import SparseMonotiles.CanonicalBindings7
public import SparseMonotiles.SkeletonClearance
public import SparseMonotiles.KeyDiameters
public import SparseMonotiles.BoundaryTransport

@[expose] public section

namespace SparseMonotiles

theorem T7_local_eq_carrier_at_integerSkeleton {p : Point 7}
    (hp : p ∈ integerSkeleton 7) : LocalSetEq p T7 (carrier 7) :=
  Canonical.localSetEq_body_carrier_of_canonical7 Canonical.everyKey7_isCanonical hp

theorem T7_keys_avoid_skeleton_quarter_ball {p : Point 7}
    (hp : p ∈ integerSkeleton 7) :
    ∀ x ∈ Metric.closedBall p (1/4 : ℝ), ∀ k ∈ keys7, x ∉ keySolid k :=
  Canonical.canonical7_keys_avoid_quarter_closedBall Canonical.everyKey7_isCanonical hp

theorem T7_each_key_diam_lt_quarter {k : KeyData 7} (hk : k ∈ keys7) :
    Metric.diam (keySolid k) < (1/4 : ℝ) :=
  Canonical.canonical7_keys_diam_lt_quarter Canonical.everyKey7_isCanonical hk

/-- The flat-skeleton germ holds in every physical tile placement. -/
theorem T7_copy_local_eq_carrier_at_integerSkeleton
    (g : Point 7 ≃ᵢ Point 7) {p : Point 7}
    (hp : p ∈ integerSkeleton 7) :
    LocalSetEq (g p) (g '' T7) (g '' carrier 7) :=
  (T7_local_eq_carrier_at_integerSkeleton hp).image_isometry g

/-- Reflections and arbitrary rotations preserve the same strict key bound. -/
theorem T7_copy_each_key_diam_lt_quarter
    (g : Point 7 ≃ᵢ Point 7) {k : KeyData 7} (hk : k ∈ keys7) :
    Metric.diam (g '' keySolid k) < (1/4 : ℝ) := by
  rw [g.diam_image]
  exact T7_each_key_diam_lt_quarter hk

#print axioms T7_copy_local_eq_carrier_at_integerSkeleton
#print axioms T7_copy_each_key_diam_lt_quarter

#print axioms T7_local_eq_carrier_at_integerSkeleton
#print axioms T7_keys_avoid_skeleton_quarter_ball
#print axioms T7_each_key_diam_lt_quarter

end SparseMonotiles
