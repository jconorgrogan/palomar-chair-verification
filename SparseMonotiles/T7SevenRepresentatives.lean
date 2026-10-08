module
public import SparseMonotiles.T7Existence205
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7
open Contact ContactInverseReuse Set
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def extraFour : Finset (Fin 408) := {0,5,30,244}

theorem extraFour_subset : extraFour ⊆ remainingAfterThree := by
  intro i hi
  simp only [extraFour, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> decide +kernel

theorem extraFour_count : extraFour.card = 4 := by decide +kernel

def remainingAfterSeven : Finset (Fin 408) := remainingAfterThree \ extraFour

theorem remainingAfterSeven_count : remainingAfterSeven.card = 201 := by
  rw [remainingAfterSeven, Finset.card_sdiff_of_subset extraFour_subset,
    remainingAfterThree_count, extraFour_count]

def checkedSeven : Finset (Fin 408) := checkedThree ∪ extraFour

def checkedOriginalThirteen : Finset (Fin 408) :=
  checkedSeven ∪ checkedSeven.image inverseIndex

theorem checkedOriginalThirteen_exact :
    checkedOriginalThirteen = {0,3,5,30,159,214,222,225,238,239,244,246,407} := by
  decide +kernel

theorem checkedOriginalThirteen_count : checkedOriginalThirteen.card = 13 := by
  rw [checkedOriginalThirteen_exact]
  decide +kernel

/-- Generic next finite assembly. The four new legality proofs remain
explicit here; the concrete endpoint binds them in a separate module. -/
theorem M7_legal_of_seven_and_remaining
    (hextra : ∀ i ∈ extraFour, IndexedData7.geometry.LegalContact (catalogRow i))
    (hrest : ∀ i ∈ remainingAfterSeven, IndexedData7.geometry.LegalContact (catalogRow i)) :
    ∀ p ∈ M7, IndexedData7.geometry.LegalContact p := by
  apply M7_legal_of_remaining205
  intro i hi
  by_cases he : i ∈ extraFour
  · exact hextra i he
  · exact hrest i (Finset.mem_sdiff.mpr ⟨hi,he⟩)

#print axioms extraFour_subset
#print axioms remainingAfterSeven_count
#print axioms checkedOriginalThirteen_exact
#print axioms M7_legal_of_seven_and_remaining
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7
