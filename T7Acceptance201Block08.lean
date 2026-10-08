module
public import T7Acceptance201Blocks
public import Acceptance185Certificate
public import Acceptance186Certificate
public import Acceptance188Certificate
public import Acceptance190Certificate
public import Acceptance192Certificate
public import Acceptance194Certificate
public import Acceptance196Certificate
public import Acceptance198Certificate
public import Acceptance200Certificate
public import Acceptance202Certificate
public import Acceptance204Certificate
public import Acceptance206Certificate
public import Acceptance208Certificate
public import Acceptance210Certificate
public import Acceptance212Certificate
public import Acceptance215Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block08_legal : ∀ i ∈ block08,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [block08, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Acceptance185Pilot7.original_entry185_legal
  · exact Acceptance186Pilot7.original_entry186_legal
  · exact Acceptance188Pilot7.original_entry188_legal
  · exact Acceptance190Pilot7.original_entry190_legal
  · exact Acceptance192Pilot7.original_entry192_legal
  · exact Acceptance194Pilot7.original_entry194_legal
  · exact Acceptance196Pilot7.original_entry196_legal
  · exact Acceptance198Pilot7.original_entry198_legal
  · exact Acceptance200Pilot7.original_entry200_legal
  · exact Acceptance202Pilot7.original_entry202_legal
  · exact Acceptance204Pilot7.original_entry204_legal
  · exact Acceptance206Pilot7.original_entry206_legal
  · exact Acceptance208Pilot7.original_entry208_legal
  · exact Acceptance210Pilot7.original_entry210_legal
  · exact Acceptance212Pilot7.original_entry212_legal
  · exact Acceptance215Pilot7.original_entry215_legal

#print axioms block08_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
