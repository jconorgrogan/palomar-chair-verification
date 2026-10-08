module

public import SparseMonotiles.KeyCompanionFeatureMatching
public import SparseMonotiles.PyramidIsometryRigidityNative

@[expose] public section

/-! # Actual key companions have an exact signed integer relative pose
Whole-key coincidence is now derived from the tiling, rather than supplied as
an input to the rigid-pyramid registration theorem.
-/
namespace SparseMonotiles
open Set Canonical

theorem T5_key_has_registered_whole_key_companion
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5) (A : tiles)
    {k : KeyData 5} (hk : k ∈ keys5) :
    ∃ B : tiles, B ≠ A ∧ ∃ l ∈ keys5,
      g A '' keySolid k=g B '' keySolid l ∧
      ∃ p : Contact.Pose 5, (g B).trans (g A).symm=p.euclidean.toIsometryEquiv := by
  obtain ⟨B,hBA,l,hl,heq⟩ := T5_key_has_whole_key_companion ht g hg A hk
  exact ⟨B,hBA,l,hl,heq,arbitrary_representatives5_registered_of_matched_key hk hl (g A) (g B) heq⟩

theorem T7_key_has_registered_whole_key_companion
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7) (A : tiles)
    {k : KeyData 7} (hk : k ∈ keys7) :
    ∃ B : tiles, B ≠ A ∧ ∃ l ∈ keys7,
      g A '' keySolid k=g B '' keySolid l ∧
      ∃ p : Contact.Pose 7, (g B).trans (g A).symm=p.euclidean.toIsometryEquiv := by
  obtain ⟨B,hBA,l,hl,heq⟩ := T7_key_has_whole_key_companion ht g hg A hk
  exact ⟨B,hBA,l,hl,heq,arbitrary_representatives7_registered_of_matched_key hk hl (g A) (g B) heq⟩

#print axioms T5_key_has_registered_whole_key_companion
#print axioms T7_key_has_registered_whole_key_companion
end SparseMonotiles
