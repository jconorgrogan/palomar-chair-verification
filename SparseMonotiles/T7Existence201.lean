module
public import SparseMonotiles.T7SevenRepresentatives
public import Acceptance0Certificate
public import Acceptance5Certificate
public import Acceptance30Certificate
public import Acceptance244Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7
open Contact ContactInverseReuse Set
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem extraFour_legal : ∀ i ∈ extraFour,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [extraFour, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact Acceptance0Pilot7.original_entry0_legal
  · exact Acceptance5Pilot7.original_entry5_legal
  · exact Acceptance30Pilot7.original_entry30_legal
  · exact Acceptance244Pilot7.original_entry244_legal

theorem checkedSeven_legal : ∀ i ∈ checkedSeven,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact checkedThree_legal i hi
  · exact extraFour_legal i hi

theorem checkedOriginalThirteen_legal : ∀ i ∈ checkedOriginalThirteen,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact checkedSeven_legal i hi
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [← inversePose_catalogRow j]
    exact legalContact_inversePose (checkedSeven_legal j hj)

theorem M7_legal_of_remaining201
    (hrest : ∀ i ∈ remainingAfterSeven, IndexedData7.geometry.LegalContact (catalogRow i)) :
    ∀ p ∈ M7, IndexedData7.geometry.LegalContact p :=
  M7_legal_of_seven_and_remaining extraFour_legal hrest

theorem complementaryProfiles_of_remaining201
    (hrest : ∀ i ∈ remainingAfterSeven, IndexedData7.geometry.LegalContact (catalogRow i))
    (A : KeyFacetAssignment keys7) : ComplementaryProfiles A M7 :=
  complementaryProfiles_of_legal_contacts M7 (M7_legal_of_remaining201 hrest) A

#print axioms extraFour_legal
#print axioms checkedOriginalThirteen_legal
#print axioms M7_legal_of_remaining201
#print axioms complementaryProfiles_of_remaining201
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7

namespace SparseMonotiles.CarrierHierarchy.Existence.Catalog7World
open Contact ContactInverseReuse

theorem hasTiling_of_forward_and_remaining201
    (forward : ForwardRules children7 M7)
    (hrest : ∀ i ∈ ProfileBridge7.remainingAfterSeven,
      IndexedData7.geometry.LegalContact (catalogRow i)) : HasTiling T7 :=
  hasTiling_of_forward_profiles forward
    (ProfileBridge7.complementaryProfiles_of_remaining201 hrest ProfileBridge7.facets)

#print axioms hasTiling_of_forward_and_remaining201
end SparseMonotiles.CarrierHierarchy.Existence.Catalog7World
