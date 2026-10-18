module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock8T3C2
public import SpectreFinite.RadiusFivePruningLiteralBlock8T3C3
public import SpectreFinite.RadiusFivePruningLiteralBlock8T3C4
public import SpectreFinite.RadiusFivePruningLiteralBlock8T3C5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq8_3_2_0 : RadiusFivePruning.stateRow8_3_2_0 = ParentOwnership.parentRow0465 := by rfl
theorem patch_mem8_3_2_0 : RadiusFivePruning.patch8_3_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0465, parentRow_mem0465, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0465_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_2_0]
  rfl
theorem row_eq8_3_2_2 : RadiusFivePruning.stateRow8_3_2_2 = ParentOwnership.parentRow0017 := by rfl
theorem patch_mem8_3_2_2 : RadiusFivePruning.patch8_3_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0017, parentRow_mem0017, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0017_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_2_2]
  rfl
theorem row_eq8_3_2_3 : RadiusFivePruning.stateRow8_3_2_3 = ParentOwnership.parentRow0018 := by rfl
theorem patch_mem8_3_2_3 : RadiusFivePruning.patch8_3_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0018, parentRow_mem0018, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0018_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_2_3]
  rfl
theorem row_eq8_3_2_4 : RadiusFivePruning.stateRow8_3_2_4 = ParentOwnership.parentRow0028 := by rfl
theorem patch_mem8_3_2_4 : RadiusFivePruning.patch8_3_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0028, parentRow_mem0028, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0028_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_2_4]
  rfl
theorem row_eq8_3_2_5 : RadiusFivePruning.stateRow8_3_2_5 = ParentOwnership.parentRow0029 := by rfl
theorem patch_mem8_3_2_5 : RadiusFivePruning.patch8_3_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0029, parentRow_mem0029, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0029_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_2_5]
  rfl
theorem row_eq8_3_2_6 : RadiusFivePruning.stateRow8_3_2_6 = ParentOwnership.parentRow0622 := by rfl
theorem patch_mem8_3_2_6 : RadiusFivePruning.patch8_3_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0622, parentRow_mem0622, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0622_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_2_6]
  rfl
theorem row_eq8_3_2_7 : RadiusFivePruning.stateRow8_3_2_7 = ParentOwnership.parentRow0621 := by rfl
theorem patch_mem8_3_2_7 : RadiusFivePruning.patch8_3_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0621, parentRow_mem0621, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0621_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_2_7]
  rfl
theorem row_eq8_3_2_8 : RadiusFivePruning.stateRow8_3_2_8 = ParentOwnership.parentRow0625 := by rfl
theorem patch_mem8_3_2_8 : RadiusFivePruning.patch8_3_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0625, parentRow_mem0625, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0625_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_2_8]
  rfl
theorem row_eq8_3_2_9 : RadiusFivePruning.stateRow8_3_2_9 = ParentOwnership.parentRow1607 := by rfl
theorem patch_mem8_3_2_9 : RadiusFivePruning.patch8_3_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1607, parentRow_mem1607, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1607_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_2_9]
  rfl
theorem row_eq8_3_2_10 : RadiusFivePruning.stateRow8_3_2_10 = ParentOwnership.parentRow0624 := by rfl
theorem patch_mem8_3_2_10 : RadiusFivePruning.patch8_3_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0624, parentRow_mem0624, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0624_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_2_10]
  rfl
theorem row_eq8_3_2_11 : RadiusFivePruning.stateRow8_3_2_11 = ParentOwnership.parentRow1606 := by rfl
theorem patch_mem8_3_2_11 : RadiusFivePruning.patch8_3_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1606, parentRow_mem1606, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1606_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_2_11]
  rfl
theorem chunk_mem8_3_2 : ∀ p ∈ RadiusFivePruning.final8_3_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_3_2, List.forall_mem_cons]
  exact ⟨patch_mem8_3_2_0,⟨patch_mem8_3_2_2,⟨patch_mem8_3_2_3,⟨patch_mem8_3_2_4,⟨patch_mem8_3_2_5,⟨patch_mem8_3_2_6,⟨patch_mem8_3_2_7,⟨patch_mem8_3_2_8,⟨patch_mem8_3_2_9,⟨patch_mem8_3_2_10,⟨patch_mem8_3_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_3_3_0 : RadiusFivePruning.stateRow8_3_3_0 = ParentOwnership.parentRow0476 := by rfl
theorem patch_mem8_3_3_0 : RadiusFivePruning.patch8_3_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0476, parentRow_mem0476, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0476_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_3_0]
  rfl
theorem row_eq8_3_3_1 : RadiusFivePruning.stateRow8_3_3_1 = ParentOwnership.parentRow0482 := by rfl
theorem patch_mem8_3_3_1 : RadiusFivePruning.patch8_3_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0482, parentRow_mem0482, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0482_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_3_1]
  rfl
theorem row_eq8_3_3_3 : RadiusFivePruning.stateRow8_3_3_3 = ParentOwnership.parentRow0480 := by rfl
theorem patch_mem8_3_3_3 : RadiusFivePruning.patch8_3_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0480, parentRow_mem0480, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0480_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_3_3]
  rfl
theorem row_eq8_3_3_4 : RadiusFivePruning.stateRow8_3_3_4 = ParentOwnership.parentRow0485 := by rfl
theorem patch_mem8_3_3_4 : RadiusFivePruning.patch8_3_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0485, parentRow_mem0485, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0485_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_3_4]
  rfl
theorem row_eq8_3_3_5 : RadiusFivePruning.stateRow8_3_3_5 = ParentOwnership.parentRow0470 := by rfl
theorem patch_mem8_3_3_5 : RadiusFivePruning.patch8_3_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0470, parentRow_mem0470, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0470_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_3_5]
  rfl
theorem row_eq8_3_3_6 : RadiusFivePruning.stateRow8_3_3_6 = ParentOwnership.parentRow0472 := by rfl
theorem patch_mem8_3_3_6 : RadiusFivePruning.patch8_3_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0472, parentRow_mem0472, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0472_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_3_6]
  rfl
theorem row_eq8_3_3_7 : RadiusFivePruning.stateRow8_3_3_7 = ParentOwnership.parentRow0620 := by rfl
theorem patch_mem8_3_3_7 : RadiusFivePruning.patch8_3_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0620, parentRow_mem0620, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0620_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_3_7]
  rfl
theorem row_eq8_3_3_8 : RadiusFivePruning.stateRow8_3_3_8 = ParentOwnership.parentRow1603 := by rfl
theorem patch_mem8_3_3_8 : RadiusFivePruning.patch8_3_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1603, parentRow_mem1603, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1603_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_3_8]
  rfl
theorem row_eq8_3_3_9 : RadiusFivePruning.stateRow8_3_3_9 = ParentOwnership.parentRow1636 := by rfl
theorem patch_mem8_3_3_9 : RadiusFivePruning.patch8_3_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1636, parentRow_mem1636, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1636_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_3_9]
  rfl
theorem row_eq8_3_3_10 : RadiusFivePruning.stateRow8_3_3_10 = ParentOwnership.parentRow0459 := by rfl
theorem patch_mem8_3_3_10 : RadiusFivePruning.patch8_3_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0459, parentRow_mem0459, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0459_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_3_10]
  rfl
theorem row_eq8_3_3_11 : RadiusFivePruning.stateRow8_3_3_11 = ParentOwnership.parentRow1637 := by rfl
theorem patch_mem8_3_3_11 : RadiusFivePruning.patch8_3_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1637, parentRow_mem1637, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1637_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_3_11]
  rfl
theorem chunk_mem8_3_3 : ∀ p ∈ RadiusFivePruning.final8_3_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_3_3, List.forall_mem_cons]
  exact ⟨patch_mem8_3_3_0,⟨patch_mem8_3_3_1,⟨patch_mem8_3_3_3,⟨patch_mem8_3_3_4,⟨patch_mem8_3_3_5,⟨patch_mem8_3_3_6,⟨patch_mem8_3_3_7,⟨patch_mem8_3_3_8,⟨patch_mem8_3_3_9,⟨patch_mem8_3_3_10,⟨patch_mem8_3_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_3_4_0 : RadiusFivePruning.stateRow8_3_4_0 = ParentOwnership.parentRow0460 := by rfl
theorem patch_mem8_3_4_0 : RadiusFivePruning.patch8_3_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0460, parentRow_mem0460, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0460_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_4_0]
  rfl
theorem row_eq8_3_4_1 : RadiusFivePruning.stateRow8_3_4_1 = ParentOwnership.parentRow0474 := by rfl
theorem patch_mem8_3_4_1 : RadiusFivePruning.patch8_3_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0474, parentRow_mem0474, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0474_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_4_1]
  rfl
theorem row_eq8_3_4_2 : RadiusFivePruning.stateRow8_3_4_2 = ParentOwnership.parentRow0466 := by rfl
theorem patch_mem8_3_4_2 : RadiusFivePruning.patch8_3_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0466, parentRow_mem0466, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0466_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_4_2]
  rfl
theorem row_eq8_3_4_3 : RadiusFivePruning.stateRow8_3_4_3 = ParentOwnership.parentRow0475 := by rfl
theorem patch_mem8_3_4_3 : RadiusFivePruning.patch8_3_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0475, parentRow_mem0475, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0475_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_4_3]
  rfl
theorem row_eq8_3_4_4 : RadiusFivePruning.stateRow8_3_4_4 = ParentOwnership.parentRow0467 := by rfl
theorem patch_mem8_3_4_4 : RadiusFivePruning.patch8_3_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0467, parentRow_mem0467, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0467_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_4_4]
  rfl
theorem row_eq8_3_4_5 : RadiusFivePruning.stateRow8_3_4_5 = ParentOwnership.parentRow1635 := by rfl
theorem patch_mem8_3_4_5 : RadiusFivePruning.patch8_3_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1635, parentRow_mem1635, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1635_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_4_5]
  rfl
theorem row_eq8_3_4_8 : RadiusFivePruning.stateRow8_3_4_8 = ParentOwnership.parentRow1604 := by rfl
theorem patch_mem8_3_4_8 : RadiusFivePruning.patch8_3_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1604, parentRow_mem1604, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1604_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_4_8]
  rfl
theorem row_eq8_3_4_9 : RadiusFivePruning.stateRow8_3_4_9 = ParentOwnership.parentRow1638 := by rfl
theorem patch_mem8_3_4_9 : RadiusFivePruning.patch8_3_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1638, parentRow_mem1638, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1638_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_4_9]
  rfl
theorem row_eq8_3_4_10 : RadiusFivePruning.stateRow8_3_4_10 = ParentOwnership.parentRow0461 := by rfl
theorem patch_mem8_3_4_10 : RadiusFivePruning.patch8_3_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0461, parentRow_mem0461, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0461_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_4_10]
  rfl
theorem row_eq8_3_4_11 : RadiusFivePruning.stateRow8_3_4_11 = ParentOwnership.parentRow1641 := by rfl
theorem patch_mem8_3_4_11 : RadiusFivePruning.patch8_3_4_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1641, parentRow_mem1641, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1641_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_4_11]
  rfl
theorem chunk_mem8_3_4 : ∀ p ∈ RadiusFivePruning.final8_3_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_3_4, List.forall_mem_cons]
  exact ⟨patch_mem8_3_4_0,⟨patch_mem8_3_4_1,⟨patch_mem8_3_4_2,⟨patch_mem8_3_4_3,⟨patch_mem8_3_4_4,⟨patch_mem8_3_4_5,⟨patch_mem8_3_4_8,⟨patch_mem8_3_4_9,⟨patch_mem8_3_4_10,⟨patch_mem8_3_4_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_3_5_0 : RadiusFivePruning.stateRow8_3_5_0 = ParentOwnership.parentRow0464 := by rfl
theorem patch_mem8_3_5_0 : RadiusFivePruning.patch8_3_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0464, parentRow_mem0464, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0464_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_5_0]
  rfl
theorem row_eq8_3_5_1 : RadiusFivePruning.stateRow8_3_5_1 = ParentOwnership.parentRow0479 := by rfl
theorem patch_mem8_3_5_1 : RadiusFivePruning.patch8_3_5_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0479, parentRow_mem0479, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0479_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_5_1]
  rfl
theorem row_eq8_3_5_2 : RadiusFivePruning.stateRow8_3_5_2 = ParentOwnership.parentRow0469 := by rfl
theorem patch_mem8_3_5_2 : RadiusFivePruning.patch8_3_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0469, parentRow_mem0469, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0469_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_5_2]
  rfl
theorem row_eq8_3_5_3 : RadiusFivePruning.stateRow8_3_5_3 = ParentOwnership.parentRow0471 := by rfl
theorem patch_mem8_3_5_3 : RadiusFivePruning.patch8_3_5_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0471, parentRow_mem0471, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0471_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_5_3]
  rfl
theorem row_eq8_3_5_4 : RadiusFivePruning.stateRow8_3_5_4 = ParentOwnership.parentRow0623 := by rfl
theorem patch_mem8_3_5_4 : RadiusFivePruning.patch8_3_5_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0623, parentRow_mem0623, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0623_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_5_4]
  rfl
theorem row_eq8_3_5_5 : RadiusFivePruning.stateRow8_3_5_5 = ParentOwnership.parentRow1605 := by rfl
theorem patch_mem8_3_5_5 : RadiusFivePruning.patch8_3_5_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1605, parentRow_mem1605, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1605_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_5_5]
  rfl
theorem row_eq8_3_5_6 : RadiusFivePruning.stateRow8_3_5_6 = ParentOwnership.parentRow1639 := by rfl
theorem patch_mem8_3_5_6 : RadiusFivePruning.patch8_3_5_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1639, parentRow_mem1639, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1639_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_5_6]
  rfl
theorem row_eq8_3_5_7 : RadiusFivePruning.stateRow8_3_5_7 = ParentOwnership.parentRow0462 := by rfl
theorem patch_mem8_3_5_7 : RadiusFivePruning.patch8_3_5_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0462, parentRow_mem0462, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0462_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_5_7]
  rfl
theorem row_eq8_3_5_8 : RadiusFivePruning.stateRow8_3_5_8 = ParentOwnership.parentRow1640 := by rfl
theorem patch_mem8_3_5_8 : RadiusFivePruning.patch8_3_5_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1640, parentRow_mem1640, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1640_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_5_8]
  rfl
theorem row_eq8_3_5_9 : RadiusFivePruning.stateRow8_3_5_9 = ParentOwnership.parentRow0463 := by rfl
theorem patch_mem8_3_5_9 : RadiusFivePruning.patch8_3_5_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0463, parentRow_mem0463, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0463_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_5_9]
  rfl
theorem chunk_mem8_3_5 : ∀ p ∈ RadiusFivePruning.final8_3_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_3_5, List.forall_mem_cons]
  exact ⟨patch_mem8_3_5_0,⟨patch_mem8_3_5_1,⟨patch_mem8_3_5_2,⟨patch_mem8_3_5_3,⟨patch_mem8_3_5_4,⟨patch_mem8_3_5_5,⟨patch_mem8_3_5_6,⟨patch_mem8_3_5_7,⟨patch_mem8_3_5_8,⟨patch_mem8_3_5_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
