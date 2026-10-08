module

public import SparseMonotiles.PyramidIsometryRigidityRegistration
public import SparseMonotiles.CanonicalBindings5
public import SparseMonotiles.CanonicalBindings7

@[expose] public section

/-!
# Arbitrary matched native keys force signed integer registration

This final bridge binds the rigidity theorem to every member of the actual
`keys5` and `keys7` lists. The two world representatives are arbitrary Euclidean
isometries. The only geometric premise left here is whole-key coincidence.
-/
namespace SparseMonotiles.Canonical
open Contact

/-- No registration premise: coincidence of any two actual T5 keys forces a registered isometry. -/
theorem nativeKey5_coincidence_is_registered {k l : KeyData 5}
    (hk : k ∈ keys5) (hl : l ∈ keys5)
    (g : Point 5 ≃ᵢ Point 5) (hg : g '' keySolid k = keySolid l) :
    ∃ p : Pose 5, g = p.euclidean.toIsometryEquiv :=
  keySolid5_coincidence_is_registered k l (everyKey5_isCanonical k hk)
    (everyKey5_isCanonical l hl) g hg

/-- No registration premise: coincidence of any two actual T7 keys forces a registered isometry. -/
theorem nativeKey7_coincidence_is_registered {k l : KeyData 7}
    (hk : k ∈ keys7) (hl : l ∈ keys7)
    (g : Point 7 ≃ᵢ Point 7) (hg : g '' keySolid k = keySolid l) :
    ∃ p : Pose 7, g = p.euclidean.toIsometryEquiv :=
  keySolid7_coincidence_is_registered k l (everyKey7_isCanonical k hk)
    (everyKey7_isCanonical l hl) g hg

/-- Equal world images give exact native-coordinate coincidence under the relative isometry. -/
theorem relative_isometry_image_of_coincidence {d : ℕ}
    (A B : Set (Point d)) (gA gB : Point d ≃ᵢ Point d) (h : gA '' A = gB '' B) :
    (gB.trans gA.symm) '' B = A := by
  calc
    (gB.trans gA.symm) '' B = gA.symm '' (gB '' B) := by
      rw [Set.image_image]
      rfl
    _ = gA.symm '' (gA '' A) := by rw [← h]
    _ = A := by ext x; simp

/-- For arbitrary chosen T5 representatives, one matched key registers their relative pose. -/
theorem arbitrary_representatives5_registered_of_matched_key {k l : KeyData 5}
    (hk : k ∈ keys5) (hl : l ∈ keys5) (gA gB : Point 5 ≃ᵢ Point 5)
    (hmatch : gA '' keySolid k = gB '' keySolid l) :
    ∃ p : Pose 5, gB.trans gA.symm = p.euclidean.toIsometryEquiv :=
  nativeKey5_coincidence_is_registered hl hk _
    (relative_isometry_image_of_coincidence _ _ gA gB hmatch)

/-- For arbitrary chosen T7 representatives, one matched key registers their relative pose. -/
theorem arbitrary_representatives7_registered_of_matched_key {k l : KeyData 7}
    (hk : k ∈ keys7) (hl : l ∈ keys7) (gA gB : Point 7 ≃ᵢ Point 7)
    (hmatch : gA '' keySolid k = gB '' keySolid l) :
    ∃ p : Pose 7, gB.trans gA.symm = p.euclidean.toIsometryEquiv :=
  nativeKey7_coincidence_is_registered hl hk _
    (relative_isometry_image_of_coincidence _ _ gA gB hmatch)

#print axioms nativeKey5_coincidence_is_registered
#print axioms nativeKey7_coincidence_is_registered
#print axioms arbitrary_representatives5_registered_of_matched_key
#print axioms arbitrary_representatives7_registered_of_matched_key

end SparseMonotiles.Canonical
