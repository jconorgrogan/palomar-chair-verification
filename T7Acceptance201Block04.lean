module
public import T7Acceptance201Blocks
public import Acceptance73Certificate
public import Acceptance74Certificate
public import Acceptance75Certificate
public import Acceptance76Certificate
public import Acceptance77Certificate
public import Acceptance79Certificate
public import Acceptance80Certificate
public import Acceptance82Certificate
public import Acceptance83Certificate
public import Acceptance85Certificate
public import Acceptance86Certificate
public import Acceptance87Certificate
public import Acceptance88Certificate
public import Acceptance89Certificate
public import Acceptance90Certificate
public import Acceptance91Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block04_legal : ∀ i ∈ block04,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [block04, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Acceptance73Pilot7.original_entry73_legal
  · exact Acceptance74Pilot7.original_entry74_legal
  · exact Acceptance75Pilot7.original_entry75_legal
  · exact Acceptance76Pilot7.original_entry76_legal
  · exact Acceptance77Pilot7.original_entry77_legal
  · exact Acceptance79Pilot7.original_entry79_legal
  · exact Acceptance80Pilot7.original_entry80_legal
  · exact Acceptance82Pilot7.original_entry82_legal
  · exact Acceptance83Pilot7.original_entry83_legal
  · exact Acceptance85Pilot7.original_entry85_legal
  · exact Acceptance86Pilot7.original_entry86_legal
  · exact Acceptance87Pilot7.original_entry87_legal
  · exact Acceptance88Pilot7.original_entry88_legal
  · exact Acceptance89Pilot7.original_entry89_legal
  · exact Acceptance90Pilot7.original_entry90_legal
  · exact Acceptance91Pilot7.original_entry91_legal

#print axioms block04_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
