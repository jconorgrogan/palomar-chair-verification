module
public import T7Acceptance201Blocks
public import Acceptance57Certificate
public import Acceptance58Certificate
public import Acceptance59Certificate
public import Acceptance60Certificate
public import Acceptance61Certificate
public import Acceptance62Certificate
public import Acceptance63Certificate
public import Acceptance64Certificate
public import Acceptance65Certificate
public import Acceptance66Certificate
public import Acceptance67Certificate
public import Acceptance68Certificate
public import Acceptance69Certificate
public import Acceptance70Certificate
public import Acceptance71Certificate
public import Acceptance72Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block03_legal : ∀ i ∈ block03,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [block03, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Acceptance57Pilot7.original_entry57_legal
  · exact Acceptance58Pilot7.original_entry58_legal
  · exact Acceptance59Pilot7.original_entry59_legal
  · exact Acceptance60Pilot7.original_entry60_legal
  · exact Acceptance61Pilot7.original_entry61_legal
  · exact Acceptance62Pilot7.original_entry62_legal
  · exact Acceptance63Pilot7.original_entry63_legal
  · exact Acceptance64Pilot7.original_entry64_legal
  · exact Acceptance65Pilot7.original_entry65_legal
  · exact Acceptance66Pilot7.original_entry66_legal
  · exact Acceptance67Pilot7.original_entry67_legal
  · exact Acceptance68Pilot7.original_entry68_legal
  · exact Acceptance69Pilot7.original_entry69_legal
  · exact Acceptance70Pilot7.original_entry70_legal
  · exact Acceptance71Pilot7.original_entry71_legal
  · exact Acceptance72Pilot7.original_entry72_legal

#print axioms block03_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
