module

public import SparseMonotiles.ContactCertificateDataIndexed5RegistryIndices

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] fullRows fullAccepted

noncomputable def frozenPoseSet : Finset (Pose 5) := RegistryIndices.registryList.toFinset
theorem full_accepted_exact_frozen : fullAccepted.toFinset = frozenPoseSet :=
  RegistryIndices.accepted_exact_frozen

theorem full_candidate_language_exact :
    ∀ p, (p ∈ fullRows.map IndexedRow.pose ∧ geometry.LegalContact p) ↔ p ∈ fullAccepted := by
  simpa only [full_output] using
    indexed_candidate_language_exact cells_eq facet_owned facet_injective full_rows_checked

theorem full_contact_language_of_complete
    (complete : ∀ p, geometry.LegalContact p → ∃ row ∈ fullRows, row.pose = p) :
    ∀ p, geometry.LegalContact p ↔ p ∈ fullAccepted := by
  simpa only [full_output] using
    indexed_contact_language_exact_of_complete cells_eq facet_owned facet_injective full_rows_checked complete

#print axioms full_rows_checked
#print axioms full_accepted_exact_frozen
#print axioms full_candidate_language_exact
end SparseMonotiles.Contact.IndexedData5
