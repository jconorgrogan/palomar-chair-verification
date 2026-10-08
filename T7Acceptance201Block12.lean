module
public import T7Acceptance201Blocks
public import Acceptance350Certificate
public import Acceptance365Certificate
public import Acceptance368Certificate
public import Acceptance369Certificate
public import Acceptance376Certificate
public import Acceptance383Certificate
public import Acceptance385Certificate
public import Acceptance401Certificate
public import Acceptance403Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block12_legal : ∀ i ∈ block12,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [block12, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Acceptance350Pilot7.original_entry350_legal
  · exact Acceptance365Pilot7.original_entry365_legal
  · exact Acceptance368Pilot7.original_entry368_legal
  · exact Acceptance369Pilot7.original_entry369_legal
  · exact Acceptance376Pilot7.original_entry376_legal
  · exact Acceptance383Pilot7.original_entry383_legal
  · exact Acceptance385Pilot7.original_entry385_legal
  · exact Acceptance401Pilot7.original_entry401_legal
  · exact Acceptance403Pilot7.original_entry403_legal

#print axioms block12_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
