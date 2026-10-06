module

public import SparseMonotiles.PrescribedContactProfilesNative
public import SparseMonotiles.AtlasReverse5

@[expose] public section

/-! # Unconditional actual T5 contact law
The reverse indexed-profile/literal-key binding is kernel checked. Every
geometric and static premise of the native physical contact law is discharged.
-/
namespace SparseMonotiles
open Set Canonical Contact CarrierHierarchy

theorem T5_prescribed_shared_facet_solid_profiles_match
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5)
    (A B : tiles) (hBA : B ≠ A) (p : Pose 5)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    (i j : Fin 160) (hshared : Shared p (IndexedData5.geometry.facet i) (IndexedData5.geometry.facet j)) :
    IndexedData5.geometry.SolidProfilesMatch p i j :=
  T5_solid_profiles_match_of_actual_key_binding ht g hg A B hBA p hp everyAtlas5Key_isLiteral i j hshared

theorem T5_prescribed_shared_facet_literal_profiles_eq
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5)
    (A B : tiles) (hBA : B ≠ A) (p : Pose 5)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    (i j : Fin 160) (hshared : Shared p (IndexedData5.geometry.facet i) (IndexedData5.geometry.facet j)) :
    (IndexedData5.geometry.profile i).image BoxKey.literal =
      ((IndexedData5.geometry.profile j).image BoxKey.literal).image (p.key IndexedData5.geometry.denominator) :=
  IndexedGeometry.literalProfiles_eq_of_solid_matches keyCode5_codedBy keyCode5_regular hshared
    (T5_prescribed_shared_facet_solid_profiles_match ht g hg A B hBA p hp i j hshared)

theorem T5_native_contact_legal
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5)
    (A B : tiles) (p : Pose 5) (hBA : B ≠ A)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    (hcontact : CellContact (rootPose 5) p) : IndexedData5.geometry.LegalContact p :=
  T5_native_contact_legal_of_actual_key_binding ht g hg A B p hBA hp hcontact everyAtlas5Key_isLiteral

#print axioms T5_prescribed_shared_facet_solid_profiles_match
#print axioms T5_prescribed_shared_facet_literal_profiles_eq
#print axioms T5_native_contact_legal
end SparseMonotiles
