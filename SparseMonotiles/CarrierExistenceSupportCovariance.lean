module

public import SparseMonotiles.KeySupportAtlas

@[expose] public section

/-! Exact covariance of closed key supports. Full finite BoxKey equality
therefore certifies both the genuine solid match and the support match used
in the keyed-body gluing theorem. -/
namespace SparseMonotiles
open Set Contact

private def supportLo {d : ℕ} (k : KeyData d) (i : Fin d) : ℚ :=
  min (k.centre i - k.radius i) (k.apex i)
private def supportHi {d : ℕ} (k : KeyData d) (i : Fin d) : ℚ :=
  max (k.centre i + k.radius i) (k.apex i)

private theorem support_eq_axisBox {d : ℕ} (k : KeyData d) :
    keyCoordinateSupport k = axisBox (supportLo k) (supportHi k) := by
  ext x
  simp only [keyCoordinateSupport, axisBox, supportLo, supportHi, Set.mem_setOf_eq,
    Rat.cast_min, Rat.cast_max, Rat.cast_sub, Rat.cast_add]

private theorem lower_support {d : ℕ} (p : Pose d) (k : KeyData d) :
    p.lower (supportLo k) (supportHi k) = supportLo (p.transformKey k) := by
  funext i
  cases hn : p.negative i
  · simp only [Pose.lower, supportLo, Pose.transformKey, Pose.rationalPoint, Pose.sign,
      hn, Bool.false_eq_true, if_false, Int.cast_one, one_mul]
    rw [show k.centre (p.perm i) + (p.shift i : ℚ) - k.radius (p.perm i) =
      (k.centre (p.perm i) - k.radius (p.perm i)) + p.shift i by ring]
    exact (min_add_add_right _ _ _).symm
  · simp only [Pose.lower, supportLo, supportHi, Pose.transformKey, Pose.rationalPoint,
      Pose.sign, hn, if_true, Int.cast_neg, Int.cast_one, neg_one_mul]
    rw [show -k.centre (p.perm i) + (p.shift i : ℚ) - k.radius (p.perm i) =
      -(k.centre (p.perm i) + k.radius (p.perm i)) + p.shift i by ring]
    rw [min_add_add_right, min_neg_neg]

private theorem upper_support {d : ℕ} (p : Pose d) (k : KeyData d) :
    p.upper (supportLo k) (supportHi k) = supportHi (p.transformKey k) := by
  funext i
  cases hn : p.negative i
  · simp only [Pose.upper, supportHi, Pose.transformKey, Pose.rationalPoint, Pose.sign,
      hn, Bool.false_eq_true, if_false, Int.cast_one, one_mul]
    rw [show k.centre (p.perm i) + (p.shift i : ℚ) + k.radius (p.perm i) =
      (k.centre (p.perm i) + k.radius (p.perm i)) + p.shift i by ring]
    exact (max_add_add_right _ _ _).symm
  · simp only [Pose.upper, supportLo, supportHi, Pose.transformKey, Pose.rationalPoint,
      Pose.sign, hn, if_true, Int.cast_neg, Int.cast_one, neg_one_mul]
    rw [show -k.centre (p.perm i) + (p.shift i : ℚ) + k.radius (p.perm i) =
      -(k.centre (p.perm i) - k.radius (p.perm i)) + p.shift i by ring]
    rw [max_add_add_right, max_neg_neg]

theorem Contact.Pose.image_keyCoordinateSupport {d : ℕ} (p : Pose d) (k : KeyData d) :
    p.euclidean '' keyCoordinateSupport k = keyCoordinateSupport (p.transformKey k) := by
  rw [support_eq_axisBox, p.image_axisBox, lower_support, upper_support,
    ← support_eq_axisBox]

@[simp] theorem keyCoordinateSupport_reverseKeyCoefficient {d : ℕ} (k : KeyData d) :
    keyCoordinateSupport (reverseKeyCoefficient k) = keyCoordinateSupport k := rfl

theorem Contact.Pose.boxKey_image_keyCoordinateSupport {d : ℕ} (p : Pose d)
    {den : ℤ} (hd : den ≠ 0) (k : BoxKey d) :
    p.euclidean '' keyCoordinateSupport (k.toKeyData den) =
      keyCoordinateSupport ((p.boxKey den k).toKeyData den) := by
  rw [p.image_keyCoordinateSupport, p.boxKey_toKeyData hd,
    keyCoordinateSupport_reverseKeyCoefficient]

theorem Contact.Pose.boxKey_match_support {d : ℕ} (p : Pose d) {den : ℤ}
    (hd : den ≠ 0) {root source : BoxKey d} (h : root = p.boxKey den source) :
    keyCoordinateSupport (root.toKeyData den) =
      p.euclidean '' keyCoordinateSupport (source.toKeyData den) := by
  rw [h, p.boxKey_image_keyCoordinateSupport hd]

#print axioms Contact.Pose.image_keyCoordinateSupport
#print axioms Contact.Pose.boxKey_match_support
end SparseMonotiles
