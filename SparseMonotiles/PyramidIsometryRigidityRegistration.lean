module

public import SparseMonotiles.PyramidIsometryRigidityReference
public import SparseMonotiles.PyramidIsometryRigidityPose

@[expose] public section

/-!
# Whole-key coincidence forces the exact registered relative pose

The hypotheses below are the already checked canonical bindings for the two
keys, and equality of the actual closed pyramid solids under an ARBITRARY
Euclidean isometry. The conclusion identifies that isometry itself with an
explicit signed integer pose. There is no pre-registration, axis-permutation,
orientation, tiling, or catalogue-completeness hypothesis.

This closes the one-matched-key / rigid-frame step. Obtaining whole-key
coincidence from local contact in an arbitrary tiling remains a separate
geometric recognition obligation.
-/
namespace SparseMonotiles.Canonical
open Contact

/-- Arbitrary whole-reference-key coincidence in dimension five fixes the full relative pose. -/
theorem referenceSolid5_coincidence_forces_relativeKeyPose
    (p q : Pose 5) (g : Point 5 ≃ᵢ Point 5)
    (hg : g '' (p.euclidean '' referenceSolid5) = q.euclidean '' referenceSolid5) :
    g = (relativeKeyPose p q).euclidean.toIsometryEquiv :=
  arbitrary_isometry_eq_relativeKeyPose referenceSolid5 referenceSolid5_isometry_stabilizer p q g hg

/-- Arbitrary whole-reference-key coincidence in dimension seven fixes the full relative pose. -/
theorem referenceSolid7_coincidence_forces_relativeKeyPose
    (p q : Pose 7) (g : Point 7 ≃ᵢ Point 7)
    (hg : g '' (p.euclidean '' referenceSolid7) = q.euclidean '' referenceSolid7) :
    g = (relativeKeyPose p q).euclidean.toIsometryEquiv :=
  arbitrary_isometry_eq_relativeKeyPose referenceSolid7 referenceSolid7_isometry_stabilizer p q g hg

/-- Actual native five-dimensional keys: whole-pyramid coincidence gives exact registration. -/
theorem keySolid5_coincidence_forces_relativeKeyPose
    (k l : KeyData 5) (p q : Pose 5)
    (hk : keySolid k = p.euclidean '' referenceSolid5)
    (hl : keySolid l = q.euclidean '' referenceSolid5)
    (g : Point 5 ≃ᵢ Point 5) (hg : g '' keySolid k = keySolid l) :
    g = (relativeKeyPose p q).euclidean.toIsometryEquiv := by
  apply referenceSolid5_coincidence_forces_relativeKeyPose p q g
  rwa [← hk, ← hl]

/-- Actual native seven-dimensional keys: whole-pyramid coincidence gives exact registration. -/
theorem keySolid7_coincidence_forces_relativeKeyPose
    (k l : KeyData 7) (p q : Pose 7)
    (hk : keySolid k = p.euclidean '' referenceSolid7)
    (hl : keySolid l = q.euclidean '' referenceSolid7)
    (g : Point 7 ≃ᵢ Point 7) (hg : g '' keySolid k = keySolid l) :
    g = (relativeKeyPose p q).euclidean.toIsometryEquiv := by
  apply referenceSolid7_coincidence_forces_relativeKeyPose p q g
  rwa [← hk, ← hl]

/-- Registration stated as membership in the signed integer pose family. -/
theorem keySolid5_coincidence_is_registered
    (k l : KeyData 5)
    (hk : ∃ p : Pose 5, keySolid k = p.euclidean '' referenceSolid5)
    (hl : ∃ q : Pose 5, keySolid l = q.euclidean '' referenceSolid5)
    (g : Point 5 ≃ᵢ Point 5) (hg : g '' keySolid k = keySolid l) :
    ∃ r : Pose 5, g = r.euclidean.toIsometryEquiv := by
  rcases hk with ⟨p, hp⟩
  rcases hl with ⟨q, hq⟩
  exact ⟨relativeKeyPose p q, keySolid5_coincidence_forces_relativeKeyPose k l p q hp hq g hg⟩

theorem keySolid7_coincidence_is_registered
    (k l : KeyData 7)
    (hk : ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7)
    (hl : ∃ q : Pose 7, keySolid l = q.euclidean '' referenceSolid7)
    (g : Point 7 ≃ᵢ Point 7) (hg : g '' keySolid k = keySolid l) :
    ∃ r : Pose 7, g = r.euclidean.toIsometryEquiv := by
  rcases hk with ⟨p, hp⟩
  rcases hl with ⟨q, hq⟩
  exact ⟨relativeKeyPose p q, keySolid7_coincidence_forces_relativeKeyPose k l p q hp hq g hg⟩

#print axioms referenceSolid5_coincidence_forces_relativeKeyPose
#print axioms referenceSolid7_coincidence_forces_relativeKeyPose
#print axioms keySolid5_coincidence_forces_relativeKeyPose
#print axioms keySolid7_coincidence_forces_relativeKeyPose
#print axioms keySolid5_coincidence_is_registered
#print axioms keySolid7_coincidence_is_registered

end SparseMonotiles.Canonical
