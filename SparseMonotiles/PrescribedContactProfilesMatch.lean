module

public import SparseMonotiles.PrescribedContactProfilesForward
public import SparseMonotiles.PrescribedContactProfilesSymmetry
public import SparseMonotiles.ContactPhysicalProfiles5
public import SparseMonotiles.ContactPhysicalProfiles7

@[expose] public section

/-! # Both physical solid-profile inclusions for a prescribed shared facet
Registration is needed only for the prescribed pair. Every other companion
is constructed and registered by K3 and identified by its actual occupied cell.
The remaining static input is the reverse encoded-profile/literal-body binding.
-/
namespace SparseMonotiles
open Set Canonical Contact CarrierHierarchy

theorem T5_solid_profiles_match_of_actual_key_binding
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5)
    (A B : tiles) (hBA : B ≠ A) (p : Pose 5)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    (hkeys : ∀ i (b : BoxKey 5), b ∈ IndexedData5.geometry.profile i → b.toKeyData 19200 ∈ keys5)
    (i j : Fin 160) (hshared : Shared p (IndexedData5.geometry.facet i) (IndexedData5.geometry.facet j)) :
    IndexedData5.geometry.SolidProfilesMatch p i j := by
  constructor
  · intro root hr
    exact T5_root_key_matches_prescribed_shared_tile ht g hg A B hBA p hp hshared hr (hkeys i root hr)
  · intro source hs
    have hpInv := reverse_relative_isometry_pose (g A) (g B) p hp
    have hsharedInv := shared_inversePose hshared
    obtain ⟨root,hr,heinv⟩ := T5_root_key_matches_prescribed_shared_tile ht g hg B A (Ne.symm hBA)
      (inversePose p) hpInv hsharedInv hs (hkeys j source hs)
    rw [inversePose_euclidean] at heinv
    have heq : p.euclidean '' keySolid (source.toKeyData 19200)=keySolid (root.toKeyData 19200) := by
      rw [heinv]
      ext x
      simp
    exact ⟨root,hr,heq.symm⟩

#print axioms T5_solid_profiles_match_of_actual_key_binding

theorem T7_solid_profiles_match_of_actual_key_binding
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7)
    (A B : tiles) (hBA : B ≠ A) (p : Pose 7)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    (hkeys : ∀ i (b : BoxKey 7), b ∈ IndexedData7.geometry.profile i → b.toKeyData 188160 ∈ keys7)
    (i j : Fin 896) (hshared : Shared p (IndexedData7.geometry.facet i) (IndexedData7.geometry.facet j)) :
    IndexedData7.geometry.SolidProfilesMatch p i j := by
  constructor
  · intro root hr
    exact T7_root_key_matches_prescribed_shared_tile ht g hg A B hBA p hp hshared hr (hkeys i root hr)
  · intro source hs
    have hpInv := reverse_relative_isometry_pose (g A) (g B) p hp
    have hsharedInv := shared_inversePose hshared
    obtain ⟨root,hr,heinv⟩ := T7_root_key_matches_prescribed_shared_tile ht g hg B A (Ne.symm hBA)
      (inversePose p) hpInv hsharedInv hs (hkeys j source hs)
    rw [inversePose_euclidean] at heinv
    have heq : p.euclidean '' keySolid (source.toKeyData 188160)=keySolid (root.toKeyData 188160) := by
      rw [heinv]
      ext x
      simp
    exact ⟨root,hr,heq.symm⟩

#print axioms T7_solid_profiles_match_of_actual_key_binding

end SparseMonotiles
