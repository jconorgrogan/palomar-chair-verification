module
public import CatalogAcceptanceRepresentatives7
public import SparseMonotiles.T7LegalContactProfiles
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7
open Contact ContactInverseReuse Set
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev checkedRepresentative : Fin 408 := 214

theorem checkedRepresentative_mem : checkedRepresentative ∈ acceptanceRepresentatives := by
  decide +kernel

def remainingAcceptanceRepresentatives : Finset (Fin 408) :=
  acceptanceRepresentatives.erase checkedRepresentative

theorem remainingAcceptanceRepresentatives_count :
    remainingAcceptanceRepresentatives.card = 207 := by
  rw [remainingAcceptanceRepresentatives, Finset.card_erase_of_mem checkedRepresentative_mem,
    acceptanceRepresentatives_count]

theorem checkedRepresentative_legal :
    IndexedData7.geometry.LegalContact (catalogRow checkedRepresentative) := by
  change IndexedData7.geometry.LegalContact (Catalog7.supplied.get ⟨214, by decide⟩)
  exact Acceptance214Pilot7.original_entry214_legal

/-- Full original-M7 legality follows once the other207 inverse representatives
are checked. The one finished wall-pose certificate is used explicitly. -/
theorem M7_legal_of_remaining_representatives
    (hlegal : ∀ i ∈ remainingAcceptanceRepresentatives,
      IndexedData7.geometry.LegalContact (catalogRow i)) :
    ∀ p ∈ M7, IndexedData7.geometry.LegalContact p := by
  apply M7_legal_of_acceptance_representatives IndexedData7.geometry
  intro i hi
  by_cases he : i = checkedRepresentative
  · subst i
    exact checkedRepresentative_legal
  · exact hlegal i (Finset.mem_erase.mpr ⟨he, hi⟩)

/-- This finite hypothesis suffices for actual solids, supports and opposite
coefficients. No rejection/exhaustive-candidate classification is needed. -/
theorem complementaryProfiles_of_remaining_representatives
    (hlegal : ∀ i ∈ remainingAcceptanceRepresentatives,
      IndexedData7.geometry.LegalContact (catalogRow i))
    (A : KeyFacetAssignment keys7) : ComplementaryProfiles A M7 :=
  complementaryProfiles_of_legal_contacts M7
    (M7_legal_of_remaining_representatives hlegal) A

#print axioms checkedRepresentative_mem
#print axioms remainingAcceptanceRepresentatives_count
#print axioms checkedRepresentative_legal
#print axioms M7_legal_of_remaining_representatives
#print axioms complementaryProfiles_of_remaining_representatives
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7
