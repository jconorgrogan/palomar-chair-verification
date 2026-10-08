module

public import SparseMonotiles.PrescribedContactProfilesMatch
public import SparseMonotiles.ContactSharedGeometry
public import SparseMonotiles.FacetAtlasCompleteness5
public import SparseMonotiles.FacetAtlasCompleteness7

@[expose] public section

/-! # Native physical unit-cell contact satisfies the exact indexed predicate
Actual physical interiors, complete facet atlases, whole-key recognition and
prescribed-neighbor profile matching discharge all geometric contact inputs.
Only the static reverse profile/literal-key binding is parameterized here.
-/
namespace SparseMonotiles
open Set Canonical Contact CarrierHierarchy

theorem T5_native_contact_legal_of_actual_key_binding
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5)
    (A B : tiles) (p : Pose 5) (hBA : B ≠ A)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    (hcontact : CellContact (rootPose 5) p)
    (hkeys : ∀ i (b : BoxKey 5), b ∈ IndexedData5.geometry.profile i → b.toKeyData 19200 ∈ keys5) :
    IndexedData5.geometry.LegalContact p := by
  have hdis : Disjoint (interior T5) (interior (p.euclidean '' T5)) := by
    have h := ht.relative_copies_interior_disjoint g hg A B hBA
    rw [hp] at h
    exact h
  have hcarrier := T5_carrier_disjoint_of_physical_interiors hdis
  obtain ⟨a,b,ha,hea,hb,heb,hshared⟩ := cellContact_root_exists_exposed_shared hcarrier hcontact
  obtain ⟨i,hfi⟩ := T5_indexed_facets_complete a ha hea
  obtain ⟨j,hfj⟩ := T5_indexed_facets_complete b hb heb
  have hsharedij : Shared p (IndexedData5.geometry.facet i) (IndexedData5.geometry.facet j) := by
    rw [hfi,hfj]
    exact hshared
  have hprofiles := T5_solid_profiles_match_of_actual_key_binding ht g hg A B hBA p hp hkeys i j hsharedij
  obtain ⟨root,hr⟩ := (profile5_checked i).1
  obtain ⟨source,hs,heq⟩ := hprofiles.1 root hr
  apply T5_legalContact_of_physical_solid_profiles hdis ⟨i,j,root,hr,source,hs,heq⟩
  intro i' j' hshared'
  exact T5_solid_profiles_match_of_actual_key_binding ht g hg A B hBA p hp hkeys i' j' hshared'

#print axioms T5_native_contact_legal_of_actual_key_binding

theorem T7_native_contact_legal_of_actual_key_binding
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7)
    (A B : tiles) (p : Pose 7) (hBA : B ≠ A)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    (hcontact : CellContact (rootPose 7) p)
    (hkeys : ∀ i (b : BoxKey 7), b ∈ IndexedData7.geometry.profile i → b.toKeyData 188160 ∈ keys7) :
    IndexedData7.geometry.LegalContact p := by
  have hdis : Disjoint (interior T7) (interior (p.euclidean '' T7)) := by
    have h := ht.relative_copies_interior_disjoint g hg A B hBA
    rw [hp] at h
    exact h
  have hcarrier := T7_carrier_disjoint_of_physical_interiors hdis
  obtain ⟨a,b,ha,hea,hb,heb,hshared⟩ := cellContact_root_exists_exposed_shared hcarrier hcontact
  obtain ⟨i,hfi⟩ := T7_indexed_facets_complete a ha hea
  obtain ⟨j,hfj⟩ := T7_indexed_facets_complete b hb heb
  have hsharedij : Shared p (IndexedData7.geometry.facet i) (IndexedData7.geometry.facet j) := by
    rw [hfi,hfj]
    exact hshared
  have hprofiles := T7_solid_profiles_match_of_actual_key_binding ht g hg A B hBA p hp hkeys i j hsharedij
  obtain ⟨root,hr⟩ := (profile7_checked i).1
  obtain ⟨source,hs,heq⟩ := hprofiles.1 root hr
  apply T7_legalContact_of_physical_solid_profiles hdis ⟨i,j,root,hr,source,hs,heq⟩
  intro i' j' hshared'
  exact T7_solid_profiles_match_of_actual_key_binding ht g hg A B hBA p hp hkeys i' j' hshared'

#print axioms T7_native_contact_legal_of_actual_key_binding

end SparseMonotiles
