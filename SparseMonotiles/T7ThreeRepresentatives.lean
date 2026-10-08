module
public import SparseMonotiles.T7ConditionalExistence
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7
open Contact ContactInverseReuse Set
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Exact original catalog representative indices removed by this bounded pass.
The legality assumptions in the generic assembly below remain explicit. -/
def remainingAfterThree : Finset (Fin 408) :=
  (remainingAcceptanceRepresentatives.erase 222).erase 238

theorem entry222_mem_remaining : (222 : Fin 408) ∈ remainingAcceptanceRepresentatives := by
  decide +kernel

theorem entry238_mem_remaining_erase222 :
    (238 : Fin 408) ∈ remainingAcceptanceRepresentatives.erase 222 := by
  decide +kernel

theorem remainingAfterThree_count : remainingAfterThree.card = 205 := by
  rw [remainingAfterThree,
    Finset.card_erase_of_mem entry238_mem_remaining_erase222,
    Finset.card_erase_of_mem entry222_mem_remaining,
    remainingAcceptanceRepresentatives_count]

def checkedThree : Finset (Fin 408) := {214, 222, 238}

def checkedOriginalRows : Finset (Fin 408) :=
  checkedThree ∪ checkedThree.image inverseIndex

theorem checkedOriginalRows_exact :
    checkedOriginalRows = {214, 222, 225, 238, 239} := by
  decide +kernel

theorem checkedOriginalRows_count : checkedOriginalRows.card = 5 := by
  rw [checkedOriginalRows_exact]
  decide +kernel

/-- Reusable finite assembly. The original checked entry214 and two explicit
new-row legality proofs discharge exactly three inverse representatives. -/
theorem M7_legal_of_three_and_remaining
    (h222 : IndexedData7.geometry.LegalContact (catalogRow 222))
    (h238 : IndexedData7.geometry.LegalContact (catalogRow 238))
    (hrest : ∀ i ∈ remainingAfterThree,
      IndexedData7.geometry.LegalContact (catalogRow i)) :
    ∀ p ∈ M7, IndexedData7.geometry.LegalContact p := by
  apply M7_legal_of_remaining_representatives
  intro i hi
  by_cases hfirst : i = 222
  · subst i
    exact h222
  by_cases hsecond : i = 238
  · subst i
    exact h238
  exact hrest i (Finset.mem_erase.mpr ⟨hsecond, Finset.mem_erase.mpr ⟨hfirst, hi⟩⟩)

theorem complementaryProfiles_of_three_and_remaining
    (h222 : IndexedData7.geometry.LegalContact (catalogRow 222))
    (h238 : IndexedData7.geometry.LegalContact (catalogRow 238))
    (hrest : ∀ i ∈ remainingAfterThree,
      IndexedData7.geometry.LegalContact (catalogRow i))
    (A : KeyFacetAssignment keys7) : ComplementaryProfiles A M7 :=
  complementaryProfiles_of_legal_contacts M7
    (M7_legal_of_three_and_remaining h222 h238 hrest) A

#print axioms remainingAfterThree_count
#print axioms checkedOriginalRows_exact
#print axioms checkedOriginalRows_count
#print axioms M7_legal_of_three_and_remaining
#print axioms complementaryProfiles_of_three_and_remaining
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7
