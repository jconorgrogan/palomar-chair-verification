module
public import T7Acceptance201Blocks
public import Acceptance297Certificate
public import Acceptance302Certificate
public import Acceptance303Certificate
public import Acceptance307Certificate
public import Acceptance310Certificate
public import Acceptance312Certificate
public import Acceptance315Certificate
public import Acceptance321Certificate
public import Acceptance322Certificate
public import Acceptance325Certificate
public import Acceptance326Certificate
public import Acceptance327Certificate
public import Acceptance329Certificate
public import Acceptance340Certificate
public import Acceptance341Certificate
public import Acceptance344Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block11_legal : ∀ i ∈ block11,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [block11, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Acceptance297Pilot7.original_entry297_legal
  · exact Acceptance302Pilot7.original_entry302_legal
  · exact Acceptance303Pilot7.original_entry303_legal
  · exact Acceptance307Pilot7.original_entry307_legal
  · exact Acceptance310Pilot7.original_entry310_legal
  · exact Acceptance312Pilot7.original_entry312_legal
  · exact Acceptance315Pilot7.original_entry315_legal
  · exact Acceptance321Pilot7.original_entry321_legal
  · exact Acceptance322Pilot7.original_entry322_legal
  · exact Acceptance325Pilot7.original_entry325_legal
  · exact Acceptance326Pilot7.original_entry326_legal
  · exact Acceptance327Pilot7.original_entry327_legal
  · exact Acceptance329Pilot7.original_entry329_legal
  · exact Acceptance340Pilot7.original_entry340_legal
  · exact Acceptance341Pilot7.original_entry341_legal
  · exact Acceptance344Pilot7.original_entry344_legal

#print axioms block11_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
