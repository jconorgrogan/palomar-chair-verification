module
public import T7Acceptance201Blocks
public import Acceptance123Certificate
public import Acceptance126Certificate
public import Acceptance127Certificate
public import Acceptance128Certificate
public import Acceptance131Certificate
public import Acceptance134Certificate
public import Acceptance137Certificate
public import Acceptance139Certificate
public import Acceptance140Certificate
public import Acceptance141Certificate
public import Acceptance142Certificate
public import Acceptance144Certificate
public import Acceptance146Certificate
public import Acceptance147Certificate
public import Acceptance148Certificate
public import Acceptance152Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block06_legal : ∀ i ∈ block06,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [block06, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Acceptance123Pilot7.original_entry123_legal
  · exact Acceptance126Pilot7.original_entry126_legal
  · exact Acceptance127Pilot7.original_entry127_legal
  · exact Acceptance128Pilot7.original_entry128_legal
  · exact Acceptance131Pilot7.original_entry131_legal
  · exact Acceptance134Pilot7.original_entry134_legal
  · exact Acceptance137Pilot7.original_entry137_legal
  · exact Acceptance139Pilot7.original_entry139_legal
  · exact Acceptance140Pilot7.original_entry140_legal
  · exact Acceptance141Pilot7.original_entry141_legal
  · exact Acceptance142Pilot7.original_entry142_legal
  · exact Acceptance144Pilot7.original_entry144_legal
  · exact Acceptance146Pilot7.original_entry146_legal
  · exact Acceptance147Pilot7.original_entry147_legal
  · exact Acceptance148Pilot7.original_entry148_legal
  · exact Acceptance152Pilot7.original_entry152_legal

#print axioms block06_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
