module
public import SparseMonotiles.T7ThreeRepresentatives
public import Acceptance222Certificate
public import Acceptance238Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7
open Contact ContactInverseReuse Set
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem checked222_legal : IndexedData7.geometry.LegalContact (catalogRow 222) := by
  change IndexedData7.geometry.LegalContact (Catalog7.supplied.get ⟨222, by decide⟩)
  exact Acceptance222Pilot7.original_entry222_legal

theorem checked238_legal : IndexedData7.geometry.LegalContact (catalogRow 238) := by
  change IndexedData7.geometry.LegalContact (Catalog7.supplied.get ⟨238, by decide⟩)
  exact Acceptance238Pilot7.original_entry238_legal

theorem checkedThree_legal : ∀ i ∈ checkedThree,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [checkedThree, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · exact checkedRepresentative_legal
  · exact checked222_legal
  · exact checked238_legal

/-- Five exact original catalog rows are now legal, including the two inverse
mates. The eight self-inverse representatives are not conflated with pairs. -/
theorem checkedOriginalRows_legal : ∀ i ∈ checkedOriginalRows,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact checkedThree_legal i hi
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [← inversePose_catalogRow j]
    exact legalContact_inversePose (checkedThree_legal j hj)

theorem M7_legal_of_remaining205
    (hrest : ∀ i ∈ remainingAfterThree,
      IndexedData7.geometry.LegalContact (catalogRow i)) :
    ∀ p ∈ M7, IndexedData7.geometry.LegalContact p :=
  M7_legal_of_three_and_remaining checked222_legal checked238_legal hrest

theorem complementaryProfiles_of_remaining205
    (hrest : ∀ i ∈ remainingAfterThree,
      IndexedData7.geometry.LegalContact (catalogRow i))
    (A : KeyFacetAssignment keys7) : ComplementaryProfiles A M7 :=
  complementaryProfiles_of_legal_contacts M7 (M7_legal_of_remaining205 hrest) A

#print axioms checked222_legal
#print axioms checked238_legal
#print axioms checkedOriginalRows_legal
#print axioms M7_legal_of_remaining205
#print axioms complementaryProfiles_of_remaining205
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7

namespace SparseMonotiles.CarrierHierarchy.Existence.Catalog7World
open Contact ContactInverseReuse

/-- Actual compact T7 existence still has exactly the stated finite forward
and205-representative hypotheses. This theorem makes no unconditional claim. -/
theorem hasTiling_of_forward_and_remaining205
    (forward : ForwardRules children7 M7)
    (hrest : ∀ i ∈ ProfileBridge7.remainingAfterThree,
      IndexedData7.geometry.LegalContact (catalogRow i)) : HasTiling T7 :=
  hasTiling_of_forward_profiles forward
    (ProfileBridge7.complementaryProfiles_of_remaining205 hrest ProfileBridge7.facets)

#print axioms hasTiling_of_forward_and_remaining205
end SparseMonotiles.CarrierHierarchy.Existence.Catalog7World
