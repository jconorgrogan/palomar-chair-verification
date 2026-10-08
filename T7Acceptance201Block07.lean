module
public import T7Acceptance201Blocks
public import Acceptance154Certificate
public import Acceptance155Certificate
public import Acceptance156Certificate
public import Acceptance157Certificate
public import Acceptance164Certificate
public import Acceptance168Certificate
public import Acceptance169Certificate
public import Acceptance170Certificate
public import Acceptance172Certificate
public import Acceptance175Certificate
public import Acceptance176Certificate
public import Acceptance177Certificate
public import Acceptance178Certificate
public import Acceptance179Certificate
public import Acceptance180Certificate
public import Acceptance183Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block07_legal : ∀ i ∈ block07,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [block07, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Acceptance154Pilot7.original_entry154_legal
  · exact Acceptance155Pilot7.original_entry155_legal
  · exact Acceptance156Pilot7.original_entry156_legal
  · exact Acceptance157Pilot7.original_entry157_legal
  · exact Acceptance164Pilot7.original_entry164_legal
  · exact Acceptance168Pilot7.original_entry168_legal
  · exact Acceptance169Pilot7.original_entry169_legal
  · exact Acceptance170Pilot7.original_entry170_legal
  · exact Acceptance172Pilot7.original_entry172_legal
  · exact Acceptance175Pilot7.original_entry175_legal
  · exact Acceptance176Pilot7.original_entry176_legal
  · exact Acceptance177Pilot7.original_entry177_legal
  · exact Acceptance178Pilot7.original_entry178_legal
  · exact Acceptance179Pilot7.original_entry179_legal
  · exact Acceptance180Pilot7.original_entry180_legal
  · exact Acceptance183Pilot7.original_entry183_legal

#print axioms block07_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
