module
public import SparseMonotiles.T7Existence201
public import T7Acceptance201Block00
public import T7Acceptance201Block01
public import T7Acceptance201Block02
public import T7Acceptance201Block03
public import T7Acceptance201Block04
public import T7Acceptance201Block05
public import T7Acceptance201Block06
public import T7Acceptance201Block07
public import T7Acceptance201Block08
public import T7Acceptance201Block09
public import T7Acceptance201Block10
public import T7Acceptance201Block11
public import T7Acceptance201Block12
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem remainingAfterSeven_legal : ∀ i ∈ remainingAfterSeven,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  rw [← blocks_cover_remainingAfterSeven] at hi
  simp only [Finset.mem_union] at hi
  rcases hi with h00 | h01 | h02 | h03 | h04 | h05 | h06 | h07 | h08 | h09 | h10 | h11 | h12
  · exact block00_legal i h00
  · exact block01_legal i h01
  · exact block02_legal i h02
  · exact block03_legal i h03
  · exact block04_legal i h04
  · exact block05_legal i h05
  · exact block06_legal i h06
  · exact block07_legal i h07
  · exact block08_legal i h08
  · exact block09_legal i h09
  · exact block10_legal i h10
  · exact block11_legal i h11
  · exact block12_legal i h12

/-- Every pose in the original, unchanged 408-row M7 catalog is legal. -/
theorem allM7_legal : ∀ p ∈ M7, IndexedData7.geometry.LegalContact p :=
  M7_legal_of_remaining201 remainingAfterSeven_legal

/-- Actual complementary profiles for every assignment of the compact keys. -/
theorem complementaryProfiles_for_assignment (A : KeyFacetAssignment keys7) :
    ComplementaryProfiles A M7 :=
  complementaryProfiles_of_remaining201 remainingAfterSeven_legal A

/-- Actual complementary profiles for the canonical compact T7 facets. -/
theorem actual_complementaryProfiles : ComplementaryProfiles facets M7 :=
  complementaryProfiles_for_assignment facets

#print axioms remainingAfterSeven_legal
#print axioms allM7_legal
#print axioms complementaryProfiles_for_assignment
#print axioms actual_complementaryProfiles
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
