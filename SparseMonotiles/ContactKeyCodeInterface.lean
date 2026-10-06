module

public import SparseMonotiles.ContactIndexedChecker
public import SparseMonotiles.KeyCovariance

@[expose] public section

/-!
Kernel-checked generic interface: static coordinate coding of reference keys.
No concrete T5/T7 binding or physical contact-law conclusion is claimed here.

The twice-centred coordinate avoids division by two:
  delta_i = 2 * centre_i - denominator * facetCentre2_i.
A shared registered facet sends delta_i to sign_i * delta_perm(i). Width and
asymmetric tangential offset are therefore encoded by functions of its absolute
value, with the offset carrying its sign. The normal apex height explicitly uses
the facet normal and the bump coefficient.

The algebraic conclusions are covariance and determination of the full signature
by centre plus coefficient. A separate corollary uses the already checked genuine
Euclidean covariance to obtain actual key-solid equality when centre agreement
and opposite material coefficient have been supplied. These premises are NOT
inferred from physical tile contact in this module. That contact-to-solid/material
step, and static bindings of these code hypotheses, remain separate obligations.
-/
namespace SparseMonotiles.Contact

structure KeyCoordinateCode where
  denominator : ℤ
  height : ℤ
  width : ℕ → ℤ
  offset : ℕ → ℤ

def KeyCoordinateCode.delta {d : ℕ} (C : KeyCoordinateCode)
    (f : Facet d) (k : BoxKey d) : ScaledPoint d :=
  fun i => 2 * k.centre i - C.denominator * f.centre2 i

def KeyCoordinateCode.oddOffset (C : KeyCoordinateCode) (u : ℤ) : ℤ :=
  u.sign * C.offset u.natAbs

def KeyCoordinateCode.signedHeight (C : KeyCoordinateCode) (b : Bool) : ℤ :=
  if b then C.height else -C.height

/-- Finite, pointwise hypotheses on one literal signature. Positivity and
nondegeneracy are deliberately not hidden in this algebraic definition. -/
def KeyCoordinateCode.Codes {d : ℕ} (C : KeyCoordinateCode)
    (f : Facet d) (k : BoxKey d) : Prop :=
  C.delta f k f.axis = 0 ∧
  (∀ i, k.radius i = C.width (C.delta f k i).natAbs) ∧
  ∀ i, k.apex i = k.centre i + C.oddOffset (C.delta f k i) +
    if i = f.axis then f.normal * C.signedHeight k.bump else 0

instance {d : ℕ} (C : KeyCoordinateCode) (f : Facet d) (k : BoxKey d) :
    Decidable (C.Codes f k) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Explicit geometric side conditions for later pyramid/height-profile use.
They are separate from code covariance and must be supplied by actual data. -/
def KeyCoordinateCode.RegularKey {d : ℕ} (C : KeyCoordinateCode)
    (f : Facet d) (k : BoxKey d) : Prop :=
  0 < C.denominator ∧ 0 < C.height ∧ k.radius f.axis = 0 ∧
  (∀ i, 0 ≤ k.radius i) ∧
  ∀ i, i ≠ f.axis → |C.oddOffset (C.delta f k i)| < k.radius i

/-- Static family-level binding, quantified only over the supplied finite
facets and keys. It does not assert physical profile faithfulness. -/
def IndexedGeometry.CodedBy {d n : ℕ} (g : IndexedGeometry d n)
    (C : KeyCoordinateCode) : Prop :=
  g.denominator = C.denominator ∧
  ∀ i, ∀ k ∈ g.profile i, C.Codes (g.facet i) k

@[simp] theorem KeyCoordinateCode.signedHeight_not (C : KeyCoordinateCode) (b : Bool) :
    C.signedHeight (!b) = -C.signedHeight b := by
  cases b <;> simp [KeyCoordinateCode.signedHeight]

@[simp] theorem KeyCoordinateCode.oddOffset_neg (C : KeyCoordinateCode) (u : ℤ) :
    C.oddOffset (-u) = -C.oddOffset u := by
  simp [KeyCoordinateCode.oddOffset]

theorem KeyCoordinateCode.oddOffset_signed {d : ℕ} (C : KeyCoordinateCode)
    (p : Pose d) (i : Fin d) (u : ℤ) :
    C.oddOffset (p.sign i * u) = p.sign i * C.oddOffset u := by
  cases h : p.negative i <;> simp [Pose.sign, h]

theorem KeyCoordinateCode.delta_boxKey {d : ℕ} (C : KeyCoordinateCode)
    {p : Pose d} {a b : Facet d} (shared : Shared p a b) (k : BoxKey d) (i : Fin d) :
    C.delta a (p.boxKey C.denominator k) i =
      p.sign i * C.delta b k (p.perm i) := by
  have hc := congrFun shared.1 i
  change a.centre2 i = p.sign i * b.centre2 (p.perm i) + 2 * p.shift i at hc
  simp only [KeyCoordinateCode.delta, Pose.boxKey, Pose.scaledPoint, hc]
  ring

/-- Signed-pose covariance of the static code, with the material coefficient
reversal belonging to opposed-normal comparison kept explicit. -/
theorem KeyCoordinateCode.codes_boxKey {d : ℕ} (C : KeyCoordinateCode)
    {p : Pose d} {a b : Facet d} (shared : Shared p a b) {k : BoxKey d}
    (coded : C.Codes b k) : C.Codes a (p.boxKey C.denominator k) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [C.delta_boxKey shared k a.axis, shared.2.1, coded.1, mul_zero]
  · intro i
    change k.radius (p.perm i) = C.width (C.delta a (p.boxKey C.denominator k) i).natAbs
    rw [coded.2.1, C.delta_boxKey shared k i]
    cases h : p.negative i <;> simp [Pose.sign, h]
  · intro i
    change p.sign i * k.apex (p.perm i) + C.denominator * p.shift i =
      p.sign i * k.centre (p.perm i) + C.denominator * p.shift i +
        C.oddOffset (C.delta a (p.boxKey C.denominator k) i) +
        if i = a.axis then a.normal * C.signedHeight (!k.bump) else 0
    rw [coded.2.2, C.delta_boxKey shared k i, C.oddOffset_signed]
    by_cases hi : i = a.axis
    · subst i
      rw [shared.2.1]
      simp only [if_true, C.signedHeight_not]
      rw [mul_add, mul_add, ← mul_assoc (p.sign a.axis) b.normal (C.signedHeight k.bump),
        shared.2.2]
      ring
    · have hpi : p.perm i ≠ b.axis := by
        intro he
        apply hi
        apply p.perm.injective
        exact he.trans shared.2.1.symm
      simp only [if_neg hi, if_neg hpi]
      ring

/-- A generic structural extensionality helper; no geometry is inferred. -/
theorem BoxKey.eq_of_all_fields {d : ℕ} {a b : BoxKey d}
    (hc : a.centre = b.centre) (hr : a.radius = b.radius)
    (ha : a.apex = b.apex) (hb : a.bump = b.bump) : a = b := by
  cases a
  cases b
  simp_all only [BoxKey.mk.injEq]

/-- At a fixed facet, centre plus coefficient determines the entire coded key. -/
theorem KeyCoordinateCode.eq_of_centre_coefficient {d : ℕ} (C : KeyCoordinateCode)
    {f : Facet d} {a b : BoxKey d} (ha : C.Codes f a) (hb : C.Codes f b)
    (hc : a.centre = b.centre) (hcoeff : a.bump = b.bump) : a = b := by
  have hu : C.delta f a = C.delta f b := by
    funext i
    simp only [KeyCoordinateCode.delta, hc]
  apply BoxKey.eq_of_all_fields hc ?_ ?_ hcoeff
  · funext i
    rw [ha.2.1, hb.2.1, hu]
  · funext i
    rw [ha.2.2, hb.2.2, hc, hu, hcoeff]

/-- This yields actual solid coincidence, not merely equality of a code label.
Centre agreement and the opposite material coefficient remain explicit inputs. -/
theorem KeyCoordinateCode.solid_image_of_centre_opposite_coefficient {d : ℕ}
    (C : KeyCoordinateCode) (den_ne : C.denominator ≠ 0)
    {p : Pose d} {a b : Facet d} {root source : BoxKey d}
    (shared : Shared p a b) (hroot : C.Codes a root) (hsource : C.Codes b source)
    (centres : root.centre = (p.boxKey C.denominator source).centre)
    (opposite : root.bump = !source.bump) :
    keySolid (root.toKeyData C.denominator) =
      p.euclidean '' keySolid (source.toKeyData C.denominator) := by
  apply p.boxKey_match_solid den_ne
  exact C.eq_of_centre_coefficient hroot (C.codes_boxKey shared hsource) centres opposite

/-- A proposed static separation hypothesis; no global injectivity or
physical profile reconstruction is smuggled into the definition. -/
def BoxKey.CentreLattice {d : ℕ} (step : ℤ) (k : BoxKey d) : Prop :=
  ∀ i, step ∣ k.centre i

def BoxKey.NarrowForLattice {d : ℕ} (step : ℤ) (k : BoxKey d) : Prop :=
  0 < step ∧ ∀ i, 0 ≤ k.radius i ∧ 2 * k.radius i < step

theorem BoxKey.centreLattice_boxKey {d : ℕ} {step den : ℤ} (den_multiple : step ∣ den)
    {k : BoxKey d} (hk : k.CentreLattice step) (p : Pose d) :
    (p.boxKey den k).CentreLattice step := by
  intro i
  rcases hk (p.perm i) with ⟨u, hu⟩
  rcases den_multiple with ⟨v, hv⟩
  refine ⟨p.sign i * u + v * p.shift i, ?_⟩
  simp only [Pose.boxKey, Pose.scaledPoint, hu, hv]
  ring

theorem BoxKey.narrowForLattice_boxKey {d : ℕ} {step den : ℤ} {k : BoxKey d}
    (hk : k.NarrowForLattice step) (p : Pose d) :
    (p.boxKey den k).NarrowForLattice step :=
  ⟨hk.1, fun i => hk.2 (p.perm i)⟩

#print axioms KeyCoordinateCode.codes_boxKey
#print axioms KeyCoordinateCode.eq_of_centre_coefficient
#print axioms KeyCoordinateCode.solid_image_of_centre_opposite_coefficient
end SparseMonotiles.Contact
