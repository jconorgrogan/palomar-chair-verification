module
public import T7Acceptance201Blocks
public import Acceptance217Certificate
public import Acceptance218Certificate
public import Acceptance219Certificate
public import Acceptance220Certificate
public import Acceptance221Certificate
public import Acceptance223Certificate
public import Acceptance226Certificate
public import Acceptance228Certificate
public import Acceptance230Certificate
public import Acceptance232Certificate
public import Acceptance234Certificate
public import Acceptance236Certificate
public import Acceptance240Certificate
public import Acceptance241Certificate
public import Acceptance245Certificate
public import Acceptance255Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block09_legal : ∀ i ∈ block09,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [block09, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Acceptance217Pilot7.original_entry217_legal
  · exact Acceptance218Pilot7.original_entry218_legal
  · exact Acceptance219Pilot7.original_entry219_legal
  · exact Acceptance220Pilot7.original_entry220_legal
  · exact Acceptance221Pilot7.original_entry221_legal
  · exact Acceptance223Pilot7.original_entry223_legal
  · exact Acceptance226Pilot7.original_entry226_legal
  · exact Acceptance228Pilot7.original_entry228_legal
  · exact Acceptance230Pilot7.original_entry230_legal
  · exact Acceptance232Pilot7.original_entry232_legal
  · exact Acceptance234Pilot7.original_entry234_legal
  · exact Acceptance236Pilot7.original_entry236_legal
  · exact Acceptance240Pilot7.original_entry240_legal
  · exact Acceptance241Pilot7.original_entry241_legal
  · exact Acceptance245Pilot7.original_entry245_legal
  · exact Acceptance255Pilot7.original_entry255_legal

#print axioms block09_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
