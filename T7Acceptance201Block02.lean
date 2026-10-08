module
public import T7Acceptance201Blocks
public import Acceptance38Certificate
public import Acceptance39Certificate
public import Acceptance40Certificate
public import Acceptance41Certificate
public import Acceptance42Certificate
public import Acceptance43Certificate
public import Acceptance44Certificate
public import Acceptance45Certificate
public import Acceptance46Certificate
public import Acceptance47Certificate
public import Acceptance48Certificate
public import Acceptance50Certificate
public import Acceptance51Certificate
public import Acceptance53Certificate
public import Acceptance55Certificate
public import Acceptance56Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block02_legal : ∀ i ∈ block02,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [block02, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Acceptance38Pilot7.original_entry38_legal
  · exact Acceptance39Pilot7.original_entry39_legal
  · exact Acceptance40Pilot7.original_entry40_legal
  · exact Acceptance41Pilot7.original_entry41_legal
  · exact Acceptance42Pilot7.original_entry42_legal
  · exact Acceptance43Pilot7.original_entry43_legal
  · exact Acceptance44Pilot7.original_entry44_legal
  · exact Acceptance45Pilot7.original_entry45_legal
  · exact Acceptance46Pilot7.original_entry46_legal
  · exact Acceptance47Pilot7.original_entry47_legal
  · exact Acceptance48Pilot7.original_entry48_legal
  · exact Acceptance50Pilot7.original_entry50_legal
  · exact Acceptance51Pilot7.original_entry51_legal
  · exact Acceptance53Pilot7.original_entry53_legal
  · exact Acceptance55Pilot7.original_entry55_legal
  · exact Acceptance56Pilot7.original_entry56_legal

#print axioms block02_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
