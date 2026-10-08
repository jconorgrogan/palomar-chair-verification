module

public import SparseMonotiles.PrescribedContactProfilesNative
public import SparseMonotiles.AtlasReverse7

@[expose] public section

/-! # Actual compact T7 contact profiles
Checked with Lean 4.35.0-rc2 on 2026-10-07, including the reverse-atlas
key binding, import/axiom audit, and leanchecker. The conclusion is the exact
indexed LegalContact predicate; contact-to-catalog classification and tiling
existence are separate obligations. See the accompanying receipts.
-/
namespace SparseMonotiles
open Set Canonical Contact CarrierHierarchy

theorem T7_prescribed_shared_facet_solid_profiles_match
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7)
    (A B : tiles) (hBA : B ≠ A) (p : Pose 7)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    (i j : Fin 896) (hshared : Shared p (IndexedData7.geometry.facet i) (IndexedData7.geometry.facet j)) :
    IndexedData7.geometry.SolidProfilesMatch p i j :=
  T7_solid_profiles_match_of_actual_key_binding ht g hg A B hBA p hp everyAtlas7Key_isLiteral i j hshared

theorem T7_prescribed_shared_facet_literal_profiles_eq
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7)
    (A B : tiles) (hBA : B ≠ A) (p : Pose 7)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    (i j : Fin 896) (hshared : Shared p (IndexedData7.geometry.facet i) (IndexedData7.geometry.facet j)) :
    (IndexedData7.geometry.profile i).image BoxKey.literal =
      ((IndexedData7.geometry.profile j).image BoxKey.literal).image (p.key IndexedData7.geometry.denominator) :=
  IndexedGeometry.literalProfiles_eq_of_solid_matches keyCode7_codedBy keyCode7_regular hshared
    (T7_prescribed_shared_facet_solid_profiles_match ht g hg A B hBA p hp i j hshared)

theorem T7_native_contact_legal
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7)
    (A B : tiles) (p : Pose 7) (hBA : B ≠ A)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    (hcontact : CellContact (rootPose 7) p) : IndexedData7.geometry.LegalContact p :=
  T7_native_contact_legal_of_actual_key_binding ht g hg A B p hBA hp hcontact everyAtlas7Key_isLiteral

#print axioms T7_prescribed_shared_facet_solid_profiles_match
#print axioms T7_prescribed_shared_facet_literal_profiles_eq
#print axioms T7_native_contact_legal
end SparseMonotiles
