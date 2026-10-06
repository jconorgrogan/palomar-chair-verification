module

public import SparseMonotiles.CanonicalBindings5
public import SparseMonotiles.SkeletonClearance
public import SparseMonotiles.KeyDiameters
public import SparseMonotiles.BoundaryTransport

@[expose] public section

namespace SparseMonotiles

theorem T5_local_eq_carrier_at_integerSkeleton {p : Point 5}
    (hp : p ∈ integerSkeleton 5) : LocalSetEq p T5 (carrier 5) :=
  Canonical.localSetEq_body_carrier_of_canonical5 Canonical.everyKey5_isCanonical hp

theorem T5_keys_avoid_skeleton_quarter_ball {p : Point 5}
    (hp : p ∈ integerSkeleton 5) :
    ∀ x ∈ Metric.closedBall p (1/4 : ℝ), ∀ k ∈ keys5, x ∉ keySolid k :=
  Canonical.canonical5_keys_avoid_quarter_closedBall Canonical.everyKey5_isCanonical hp

theorem T5_each_key_diam_lt_quarter {k : KeyData 5} (hk : k ∈ keys5) :
    Metric.diam (keySolid k) < (1/4 : ℝ) :=
  Canonical.canonical5_keys_diam_lt_quarter Canonical.everyKey5_isCanonical hk

/-- The flat-skeleton germ holds in every physical tile placement. -/
theorem T5_copy_local_eq_carrier_at_integerSkeleton
    (g : Point 5 ≃ᵢ Point 5) {p : Point 5}
    (hp : p ∈ integerSkeleton 5) :
    LocalSetEq (g p) (g '' T5) (g '' carrier 5) :=
  (T5_local_eq_carrier_at_integerSkeleton hp).image_isometry g

/-- Reflections and arbitrary rotations preserve the same strict key bound. -/
theorem T5_copy_each_key_diam_lt_quarter
    (g : Point 5 ≃ᵢ Point 5) {k : KeyData 5} (hk : k ∈ keys5) :
    Metric.diam (g '' keySolid k) < (1/4 : ℝ) := by
  rw [g.diam_image]
  exact T5_each_key_diam_lt_quarter hk

#print axioms T5_copy_local_eq_carrier_at_integerSkeleton
#print axioms T5_copy_each_key_diam_lt_quarter

#print axioms T5_local_eq_carrier_at_integerSkeleton
#print axioms T5_keys_avoid_skeleton_quarter_ball
#print axioms T5_each_key_diam_lt_quarter

end SparseMonotiles
