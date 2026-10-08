module
public import T7Acceptance201Blocks
public import Acceptance19Certificate
public import Acceptance20Certificate
public import Acceptance21Certificate
public import Acceptance22Certificate
public import Acceptance23Certificate
public import Acceptance24Certificate
public import Acceptance26Certificate
public import Acceptance27Certificate
public import Acceptance29Certificate
public import Acceptance31Certificate
public import Acceptance32Certificate
public import Acceptance33Certificate
public import Acceptance34Certificate
public import Acceptance35Certificate
public import Acceptance36Certificate
public import Acceptance37Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block01_legal : ∀ i ∈ block01,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [block01, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Acceptance19Pilot7.original_entry19_legal
  · exact Acceptance20Pilot7.original_entry20_legal
  · exact Acceptance21Pilot7.original_entry21_legal
  · exact Acceptance22Pilot7.original_entry22_legal
  · exact Acceptance23Pilot7.original_entry23_legal
  · exact Acceptance24Pilot7.original_entry24_legal
  · exact Acceptance26Pilot7.original_entry26_legal
  · exact Acceptance27Pilot7.original_entry27_legal
  · exact Acceptance29Pilot7.original_entry29_legal
  · exact Acceptance31Pilot7.original_entry31_legal
  · exact Acceptance32Pilot7.original_entry32_legal
  · exact Acceptance33Pilot7.original_entry33_legal
  · exact Acceptance34Pilot7.original_entry34_legal
  · exact Acceptance35Pilot7.original_entry35_legal
  · exact Acceptance36Pilot7.original_entry36_legal
  · exact Acceptance37Pilot7.original_entry37_legal

#print axioms block01_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
