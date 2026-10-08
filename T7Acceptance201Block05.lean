module
public import T7Acceptance201Blocks
public import Acceptance92Certificate
public import Acceptance97Certificate
public import Acceptance98Certificate
public import Acceptance99Certificate
public import Acceptance103Certificate
public import Acceptance106Certificate
public import Acceptance107Certificate
public import Acceptance108Certificate
public import Acceptance109Certificate
public import Acceptance110Certificate
public import Acceptance111Certificate
public import Acceptance114Certificate
public import Acceptance115Certificate
public import Acceptance117Certificate
public import Acceptance118Certificate
public import Acceptance119Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block05_legal : ∀ i ∈ block05,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [block05, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Acceptance92Pilot7.original_entry92_legal
  · exact Acceptance97Pilot7.original_entry97_legal
  · exact Acceptance98Pilot7.original_entry98_legal
  · exact Acceptance99Pilot7.original_entry99_legal
  · exact Acceptance103Pilot7.original_entry103_legal
  · exact Acceptance106Pilot7.original_entry106_legal
  · exact Acceptance107Pilot7.original_entry107_legal
  · exact Acceptance108Pilot7.original_entry108_legal
  · exact Acceptance109Pilot7.original_entry109_legal
  · exact Acceptance110Pilot7.original_entry110_legal
  · exact Acceptance111Pilot7.original_entry111_legal
  · exact Acceptance114Pilot7.original_entry114_legal
  · exact Acceptance115Pilot7.original_entry115_legal
  · exact Acceptance117Pilot7.original_entry117_legal
  · exact Acceptance118Pilot7.original_entry118_legal
  · exact Acceptance119Pilot7.original_entry119_legal

#print axioms block05_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
