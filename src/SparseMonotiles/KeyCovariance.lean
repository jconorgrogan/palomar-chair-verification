module

public import SparseMonotiles.Model
public import SparseMonotiles.ContactChecker
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
Exact Euclidean covariance of the actual rectangular-pyramid keys in `Model`.
A registered signed permutation and integral translation is realized as an
`AffineIsometryEquiv`, not just as an action on a finite encoding. Geometric
transport preserves `bump`; the Boolean reversal in `Pose.boxKey` belongs only
to opposed-normal contact comparison, and is kept explicit below.
-/
namespace SparseMonotiles.Contact

/-- The signed coordinate permutation, with the checker's output-row convention. -/
noncomputable def Pose.euclideanLinear {d : ℕ} (p : Pose d) :
    Point d ≃ₗᵢ[ℝ] Point d :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p.perm.symm).trans
    (LinearIsometryEquiv.piLpCongrRight 2 fun i =>
      if p.negative i then LinearIsometryEquiv.neg ℝ
      else LinearIsometryEquiv.refl ℝ ℝ)

/-- The actual Euclidean affine isometry represented by a registered pose. -/
noncomputable def Pose.euclidean {d : ℕ} (p : Pose d) :
    Point d ≃ᵃⁱ[ℝ] Point d :=
  p.euclideanLinear.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ (Point d)
      (SparseMonotiles.rationalPoint fun i => (p.shift i : ℚ)))

@[simp] theorem Pose.euclidean_apply {d : ℕ} (p : Pose d) (x : Point d) (i : Fin d) :
    p.euclidean x i = (p.sign i : ℝ) * x (p.perm i) + (p.shift i : ℝ) := by
  change ((p.shift i : ℚ) : ℝ) +
    (if p.negative i then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ)
      else LinearIsometryEquiv.refl ℝ ℝ) (x (p.perm i)) = _
  cases h : p.negative i <;> simp [Pose.sign, h, add_comm]

/-- Rational coordinates commute exactly with the genuine Euclidean action. -/
@[simp] theorem Pose.euclidean_rationalPoint {d : ℕ} (p : Pose d) (q : Fin d → ℚ) :
    p.euclidean (SparseMonotiles.rationalPoint q) =
      SparseMonotiles.rationalPoint (p.rationalPoint q) := by
  ext i
  rw [Pose.euclidean_apply]
  simp [SparseMonotiles.rationalPoint, Pose.rationalPoint]

/-- Closed coordinate box with exact rational lower and upper endpoints. -/
def axisBox {d : ℕ} (lo hi : Fin d → ℚ) : Set (Point d) :=
  {x | ∀ i, (lo i : ℝ) ≤ x i ∧ x i ≤ (hi i : ℝ)}

/-- Negative output rows exchange the two endpoint roles. -/
def Pose.lower {d : ℕ} (p : Pose d) (lo hi : Fin d → ℚ) : Fin d → ℚ :=
  fun i => if p.negative i then -hi (p.perm i) + (p.shift i : ℚ)
    else lo (p.perm i) + (p.shift i : ℚ)

def Pose.upper {d : ℕ} (p : Pose d) (lo hi : Fin d → ℚ) : Fin d → ℚ :=
  fun i => if p.negative i then -lo (p.perm i) + (p.shift i : ℚ)
    else hi (p.perm i) + (p.shift i : ℚ)

theorem Pose.axisBox_coordinate_iff {d : ℕ} (p : Pose d) (lo hi : Fin d → ℚ)
    (x : Point d) (i : Fin d) :
    ((p.lower lo hi i : ℝ) ≤ p.euclidean x i ∧
      p.euclidean x i ≤ (p.upper lo hi i : ℝ)) ↔
    ((lo (p.perm i) : ℝ) ≤ x (p.perm i) ∧ x (p.perm i) ≤ (hi (p.perm i) : ℝ)) := by
  rw [Pose.euclidean_apply]
  cases h : p.negative i <;>
    simp only [Pose.lower, Pose.upper, Pose.sign, h, Bool.false_eq_true,
      if_false, if_true, Rat.cast_add, Rat.cast_neg,
      Rat.cast_intCast, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] <;>
    constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith

/-- No positivity assumption is needed: empty boxes are transported correctly too. -/
theorem Pose.euclidean_mem_axisBox {d : ℕ} (p : Pose d) (lo hi : Fin d → ℚ)
    (x : Point d) :
    p.euclidean x ∈ axisBox (p.lower lo hi) (p.upper lo hi) ↔ x ∈ axisBox lo hi := by
  constructor
  · intro h j
    obtain ⟨i, rfl⟩ := p.perm.surjective j
    exact (p.axisBox_coordinate_iff lo hi x i).mp (h i)
  · intro h i
    exact (p.axisBox_coordinate_iff lo hi x i).mpr (h (p.perm i))

/-- Exact image theorem, including the endpoint reversal in negative rows. -/
theorem Pose.image_axisBox {d : ℕ} (p : Pose d) (lo hi : Fin d → ℚ) :
    p.euclidean '' axisBox lo hi = axisBox (p.lower lo hi) (p.upper lo hi) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (p.euclidean_mem_axisBox lo hi x).mpr hx
  · intro hy
    obtain ⟨x, rfl⟩ := p.euclidean.surjective y
    exact ⟨x, (p.euclidean_mem_axisBox lo hi x).mp hy, rfl⟩

/-- A key's geometric motion preserves its bump/dent tag. -/
def Pose.transformKey {d : ℕ} (p : Pose d) (k : KeyData d) : KeyData d where
  centre := p.rationalPoint k.centre
  radius := fun i => k.radius (p.perm i)
  apex := p.rationalPoint k.apex
  bump := k.bump

@[simp] theorem Pose.transformKey_bump {d : ℕ} (p : Pose d) (k : KeyData d) :
    (p.transformKey k).bump = k.bump := rfl

theorem keyBase_eq_axisBox {d : ℕ} (k : KeyData d) :
    keyBase k = axisBox (fun i => k.centre i - k.radius i)
      (fun i => k.centre i + k.radius i) := by
  ext x
  constructor
  · intro h i
    have hi := abs_le.mp (h i)
    simp only [Rat.cast_sub, Rat.cast_add]
    constructor <;> linarith [hi.1, hi.2]
  · intro h i
    have hi := h i
    simp only [Rat.cast_sub, Rat.cast_add] at hi
    apply abs_le.mpr
    constructor <;> linarith [hi.1, hi.2]

theorem Pose.lower_key {d : ℕ} (p : Pose d) (k : KeyData d) :
    p.lower (fun i => k.centre i - k.radius i) (fun i => k.centre i + k.radius i) =
      fun i => (p.transformKey k).centre i - (p.transformKey k).radius i := by
  funext i
  cases h : p.negative i <;> simp [Pose.lower, Pose.transformKey, Pose.rationalPoint,
    Pose.sign, h] <;> ring

theorem Pose.upper_key {d : ℕ} (p : Pose d) (k : KeyData d) :
    p.upper (fun i => k.centre i - k.radius i) (fun i => k.centre i + k.radius i) =
      fun i => (p.transformKey k).centre i + (p.transformKey k).radius i := by
  funext i
  cases h : p.negative i <;> simp [Pose.upper, Pose.transformKey, Pose.rationalPoint,
    Pose.sign, h] <;> ring

/-- Covariance of the base used by the actual Euclidean body definition. -/
theorem Pose.image_keyBase {d : ℕ} (p : Pose d) (k : KeyData d) :
    p.euclidean '' keyBase k = keyBase (p.transformKey k) := by
  rw [keyBase_eq_axisBox, p.image_axisBox, p.lower_key, p.upper_key,
    ← keyBase_eq_axisBox]

/-- Covariance of the whole convex pyramid, not merely of its finite signature. -/
theorem Pose.image_keySolid {d : ℕ} (p : Pose d) (k : KeyData d) :
    p.euclidean '' keySolid k = keySolid (p.transformKey k) := by
  unfold keySolid
  rw [show (p.euclidean : Point d → Point d) =
    p.euclidean.toAffineEquiv.toAffineMap from rfl]
  rw [AffineMap.image_convexHull]
  change convexHull ℝ (p.euclidean '' insert (SparseMonotiles.rationalPoint k.apex)
    (keyBase k)) = _
  rw [Set.image_insert_eq, p.euclidean_rationalPoint, p.image_keyBase]
  rfl

/-- Physical bump and dent unions transform separately, with unchanged tags. -/
theorem Pose.image_keyUnion {d : ℕ} (p : Pose d) (ks : List (KeyData d)) (b : Bool) :
    p.euclidean '' keyUnion ks b = keyUnion (ks.map p.transformKey) b := by
  ext y
  constructor
  · rintro ⟨x, ⟨k, hk, hb, hx⟩, rfl⟩
    refine ⟨p.transformKey k, List.mem_map.mpr ⟨k, hk, rfl⟩, hb, ?_⟩
    rw [← p.image_keySolid]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨k', hk', hb, hy⟩
    rcases List.mem_map.mp hk' with ⟨k, hk, rfl⟩
    rw [← p.image_keySolid] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, ⟨k, hk, hb, hx⟩, rfl⟩

/-- Covariance extends through the union, dent subtraction, and boundary closure
in the actual body. The carrier is transported, never assumed pose-invariant. -/
theorem Pose.image_body {d : ℕ} (p : Pose d) (ks : List (KeyData d)) :
    p.euclidean '' body ks =
      closure ((p.euclidean '' carrier d ∪ keyUnion (ks.map p.transformKey) true) \
        keyUnion (ks.map p.transformKey) false) := by
  unfold body
  rw [show (p.euclidean : Point d → Point d) = p.euclidean.toHomeomorph from rfl]
  rw [Homeomorph.image_closure]
  change closure (p.euclidean '' ((carrier d ∪ keyUnion ks true) \ keyUnion ks false)) = _
  rw [Set.image_diff p.euclidean.injective, Set.image_union,
    p.image_keyUnion, p.image_keyUnion]
  rfl

/-- Decode the integer box certificate into precisely the rational `Model` key. -/
def BoxKey.toKeyData {d : ℕ} (den : ℤ) (k : BoxKey d) : KeyData d where
  centre := rationalVertex den k.centre
  radius := rationalVertex den k.radius
  apex := rationalVertex den k.apex
  bump := k.bump

/-- An explicit coefficient reversal, separate from physical Euclidean motion. -/
def reverseKeyCoefficient {d : ℕ} (k : KeyData d) : KeyData d :=
  { k with bump := !k.bump }

@[simp] theorem keyBase_reverseKeyCoefficient {d : ℕ} (k : KeyData d) :
    keyBase (reverseKeyCoefficient k) = keyBase k := rfl

@[simp] theorem keySolid_reverseKeyCoefficient {d : ℕ} (k : KeyData d) :
    keySolid (reverseKeyCoefficient k) = keySolid k := rfl

/-- Denominator clearing agrees with geometry; only the contact coefficient flips. -/
theorem Pose.boxKey_toKeyData {d : ℕ} (p : Pose d) {den : ℤ} (hd : den ≠ 0)
    (k : BoxKey d) :
    (p.boxKey den k).toKeyData den = reverseKeyCoefficient (p.transformKey (k.toKeyData den)) := by
  cases k with
  | mk centre radius apex bump =>
      simp only [BoxKey.toKeyData, Pose.boxKey, Pose.transformKey, reverseKeyCoefficient]
      rw [rationalVertex_transformed p hd centre, rationalVertex_transformed p hd apex]
      rfl

/-- Integer base-box certificates also transport the actual closed Euclidean base. -/
theorem Pose.boxKey_image_keyBase {d : ℕ} (p : Pose d) {den : ℤ} (hd : den ≠ 0)
    (k : BoxKey d) :
    p.euclidean '' keyBase (k.toKeyData den) = keyBase ((p.boxKey den k).toKeyData den) := by
  rw [p.image_keyBase, p.boxKey_toKeyData hd, keyBase_reverseKeyCoefficient]

/-- A finite transformed-box equality certifies equality of actual pyramid solids. -/
theorem Pose.boxKey_image_keySolid {d : ℕ} (p : Pose d) {den : ℤ} (hd : den ≠ 0)
    (k : BoxKey d) :
    p.euclidean '' keySolid (k.toKeyData den) = keySolid ((p.boxKey den k).toKeyData den) := by
  rw [p.image_keySolid, p.boxKey_toKeyData hd, keySolid_reverseKeyCoefficient]

theorem Pose.boxKey_match_solid {d : ℕ} (p : Pose d) {den : ℤ} (hd : den ≠ 0)
    {root source : BoxKey d} (h : root = p.boxKey den source) :
    keySolid (root.toKeyData den) = p.euclidean '' keySolid (source.toKeyData den) := by
  rw [h, p.boxKey_image_keySolid hd]

/-- The opposed-normal finite convention really reverses the Boolean coefficient. -/
theorem Pose.boxKey_match_coefficient {d : ℕ} (p : Pose d) (den : ℤ)
    {root source : BoxKey d} (h : root = p.boxKey den source) : root.bump = !source.bump := by
  rw [h]
  rfl

#print axioms Pose.euclidean_rationalPoint
#print axioms Pose.image_axisBox
#print axioms Pose.image_keyBase
#print axioms Pose.image_keySolid
#print axioms Pose.image_body
#print axioms Pose.boxKey_toKeyData
#print axioms Pose.boxKey_match_solid

end SparseMonotiles.Contact
