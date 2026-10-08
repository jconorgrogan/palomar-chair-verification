module
public import T7Acceptance201Blocks
public import Acceptance258Certificate
public import Acceptance266Certificate
public import Acceptance267Certificate
public import Acceptance269Certificate
public import Acceptance270Certificate
public import Acceptance273Certificate
public import Acceptance274Certificate
public import Acceptance276Certificate
public import Acceptance277Certificate
public import Acceptance281Certificate
public import Acceptance283Certificate
public import Acceptance285Certificate
public import Acceptance286Certificate
public import Acceptance290Certificate
public import Acceptance294Certificate
public import Acceptance296Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block10_legal : ∀ i ∈ block10,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [block10, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Acceptance258Pilot7.original_entry258_legal
  · exact Acceptance266Pilot7.original_entry266_legal
  · exact Acceptance267Pilot7.original_entry267_legal
  · exact Acceptance269Pilot7.original_entry269_legal
  · exact Acceptance270Pilot7.original_entry270_legal
  · exact Acceptance273Pilot7.original_entry273_legal
  · exact Acceptance274Pilot7.original_entry274_legal
  · exact Acceptance276Pilot7.original_entry276_legal
  · exact Acceptance277Pilot7.original_entry277_legal
  · exact Acceptance281Pilot7.original_entry281_legal
  · exact Acceptance283Pilot7.original_entry283_legal
  · exact Acceptance285Pilot7.original_entry285_legal
  · exact Acceptance286Pilot7.original_entry286_legal
  · exact Acceptance290Pilot7.original_entry290_legal
  · exact Acceptance294Pilot7.original_entry294_legal
  · exact Acceptance296Pilot7.original_entry296_legal

#print axioms block10_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
