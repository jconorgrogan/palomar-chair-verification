module
public import T7Acceptance201Blocks
public import Acceptance1Certificate
public import Acceptance2Certificate
public import Acceptance4Certificate
public import Acceptance6Certificate
public import Acceptance7Certificate
public import Acceptance8Certificate
public import Acceptance9Certificate
public import Acceptance10Certificate
public import Acceptance11Certificate
public import Acceptance12Certificate
public import Acceptance13Certificate
public import Acceptance14Certificate
public import Acceptance15Certificate
public import Acceptance16Certificate
public import Acceptance17Certificate
public import Acceptance18Certificate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block00_legal : ∀ i ∈ block00,
    IndexedData7.geometry.LegalContact (catalogRow i) := by
  intro i hi
  simp only [block00, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Acceptance1Pilot7.original_entry1_legal
  · exact Acceptance2Pilot7.original_entry2_legal
  · exact Acceptance4Pilot7.original_entry4_legal
  · exact Acceptance6Pilot7.original_entry6_legal
  · exact Acceptance7Pilot7.original_entry7_legal
  · exact Acceptance8Pilot7.original_entry8_legal
  · exact Acceptance9Pilot7.original_entry9_legal
  · exact Acceptance10Pilot7.original_entry10_legal
  · exact Acceptance11Pilot7.original_entry11_legal
  · exact Acceptance12Pilot7.original_entry12_legal
  · exact Acceptance13Pilot7.original_entry13_legal
  · exact Acceptance14Pilot7.original_entry14_legal
  · exact Acceptance15Pilot7.original_entry15_legal
  · exact Acceptance16Pilot7.original_entry16_legal
  · exact Acceptance17Pilot7.original_entry17_legal
  · exact Acceptance18Pilot7.original_entry18_legal

#print axioms block00_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
