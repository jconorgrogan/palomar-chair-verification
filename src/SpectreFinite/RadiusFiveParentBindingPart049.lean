module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock7T5C1
public import SpectreFinite.RadiusFivePruningLiteralBlock7T5C2
public import SpectreFinite.RadiusFivePruningLiteralBlock7T5C3
public import SpectreFinite.RadiusFivePruningLiteralBlock7T5C4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq7_5_1_0 : RadiusFivePruning.stateRow7_5_1_0 = ParentOwnership.parentRow1535 := by rfl
theorem patch_mem7_5_1_0 : RadiusFivePruning.patch7_5_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1535, parentRow_mem1535, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1535_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_1_0]
  rfl
theorem row_eq7_5_1_2 : RadiusFivePruning.stateRow7_5_1_2 = ParentOwnership.parentRow1537 := by rfl
theorem patch_mem7_5_1_2 : RadiusFivePruning.patch7_5_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1537, parentRow_mem1537, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1537_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_1_2]
  rfl
theorem row_eq7_5_1_3 : RadiusFivePruning.stateRow7_5_1_3 = ParentOwnership.parentRow1538 := by rfl
theorem patch_mem7_5_1_3 : RadiusFivePruning.patch7_5_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1538, parentRow_mem1538, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1538_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_1_3]
  rfl
theorem row_eq7_5_1_4 : RadiusFivePruning.stateRow7_5_1_4 = ParentOwnership.parentRow0820 := by rfl
theorem patch_mem7_5_1_4 : RadiusFivePruning.patch7_5_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0820, parentRow_mem0820, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0820_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_1_4]
  rfl
theorem row_eq7_5_1_5 : RadiusFivePruning.stateRow7_5_1_5 = ParentOwnership.parentRow0821 := by rfl
theorem patch_mem7_5_1_5 : RadiusFivePruning.patch7_5_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0821, parentRow_mem0821, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0821_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_1_5]
  rfl
theorem row_eq7_5_1_6 : RadiusFivePruning.stateRow7_5_1_6 = ParentOwnership.parentRow1580 := by rfl
theorem patch_mem7_5_1_6 : RadiusFivePruning.patch7_5_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1580, parentRow_mem1580, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1580_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_1_6]
  rfl
theorem row_eq7_5_1_9 : RadiusFivePruning.stateRow7_5_1_9 = ParentOwnership.parentRow1588 := by rfl
theorem patch_mem7_5_1_9 : RadiusFivePruning.patch7_5_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1588, parentRow_mem1588, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1588_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_1_9]
  rfl
theorem row_eq7_5_1_10 : RadiusFivePruning.stateRow7_5_1_10 = ParentOwnership.parentRow1589 := by rfl
theorem patch_mem7_5_1_10 : RadiusFivePruning.patch7_5_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1589, parentRow_mem1589, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1589_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_1_10]
  rfl
theorem row_eq7_5_1_11 : RadiusFivePruning.stateRow7_5_1_11 = ParentOwnership.parentRow1544 := by rfl
theorem patch_mem7_5_1_11 : RadiusFivePruning.patch7_5_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1544, parentRow_mem1544, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1544_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_1_11]
  rfl
theorem chunk_mem7_5_1 : ∀ p ∈ RadiusFivePruning.final7_5_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_5_1, List.forall_mem_cons]
  exact ⟨patch_mem7_5_1_0,⟨patch_mem7_5_1_2,⟨patch_mem7_5_1_3,⟨patch_mem7_5_1_4,⟨patch_mem7_5_1_5,⟨patch_mem7_5_1_6,⟨patch_mem7_5_1_9,⟨patch_mem7_5_1_10,⟨patch_mem7_5_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_5_2_0 : RadiusFivePruning.stateRow7_5_2_0 = ParentOwnership.parentRow1545 := by rfl
theorem patch_mem7_5_2_0 : RadiusFivePruning.patch7_5_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1545, parentRow_mem1545, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1545_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_2_0]
  rfl
theorem row_eq7_5_2_1 : RadiusFivePruning.stateRow7_5_2_1 = ParentOwnership.parentRow1548 := by rfl
theorem patch_mem7_5_2_1 : RadiusFivePruning.patch7_5_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1548, parentRow_mem1548, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1548_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_2_1]
  rfl
theorem row_eq7_5_2_2 : RadiusFivePruning.stateRow7_5_2_2 = ParentOwnership.parentRow1549 := by rfl
theorem patch_mem7_5_2_2 : RadiusFivePruning.patch7_5_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1549, parentRow_mem1549, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1549_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_2_2]
  rfl
theorem row_eq7_5_2_3 : RadiusFivePruning.stateRow7_5_2_3 = ParentOwnership.parentRow1590 := by rfl
theorem patch_mem7_5_2_3 : RadiusFivePruning.patch7_5_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1590, parentRow_mem1590, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1590_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_2_3]
  rfl
theorem row_eq7_5_2_4 : RadiusFivePruning.stateRow7_5_2_4 = ParentOwnership.parentRow1546 := by rfl
theorem patch_mem7_5_2_4 : RadiusFivePruning.patch7_5_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1546, parentRow_mem1546, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1546_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_2_4]
  rfl
theorem row_eq7_5_2_5 : RadiusFivePruning.stateRow7_5_2_5 = ParentOwnership.parentRow1547 := by rfl
theorem patch_mem7_5_2_5 : RadiusFivePruning.patch7_5_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1547, parentRow_mem1547, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1547_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_2_5]
  rfl
theorem row_eq7_5_2_6 : RadiusFivePruning.stateRow7_5_2_6 = ParentOwnership.parentRow1550 := by rfl
theorem patch_mem7_5_2_6 : RadiusFivePruning.patch7_5_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1550, parentRow_mem1550, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1550_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_2_6]
  rfl
theorem row_eq7_5_2_8 : RadiusFivePruning.stateRow7_5_2_8 = ParentOwnership.parentRow1570 := by rfl
theorem patch_mem7_5_2_8 : RadiusFivePruning.patch7_5_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1570, parentRow_mem1570, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1570_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_2_8]
  rfl
theorem row_eq7_5_2_10 : RadiusFivePruning.stateRow7_5_2_10 = ParentOwnership.parentRow1531 := by rfl
theorem patch_mem7_5_2_10 : RadiusFivePruning.patch7_5_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1531, parentRow_mem1531, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1531_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_2_10]
  rfl
theorem row_eq7_5_2_11 : RadiusFivePruning.stateRow7_5_2_11 = ParentOwnership.parentRow0818 := by rfl
theorem patch_mem7_5_2_11 : RadiusFivePruning.patch7_5_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0818, parentRow_mem0818, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0818_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_2_11]
  rfl
theorem chunk_mem7_5_2 : ∀ p ∈ RadiusFivePruning.final7_5_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_5_2, List.forall_mem_cons]
  exact ⟨patch_mem7_5_2_0,⟨patch_mem7_5_2_1,⟨patch_mem7_5_2_2,⟨patch_mem7_5_2_3,⟨patch_mem7_5_2_4,⟨patch_mem7_5_2_5,⟨patch_mem7_5_2_6,⟨patch_mem7_5_2_8,⟨patch_mem7_5_2_10,⟨patch_mem7_5_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_5_3_0 : RadiusFivePruning.stateRow7_5_3_0 = ParentOwnership.parentRow2099 := by rfl
theorem patch_mem7_5_3_0 : RadiusFivePruning.patch7_5_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2099, parentRow_mem2099, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2099_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_3_0]
  rfl
theorem row_eq7_5_3_1 : RadiusFivePruning.stateRow7_5_3_1 = ParentOwnership.parentRow2101 := by rfl
theorem patch_mem7_5_3_1 : RadiusFivePruning.patch7_5_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2101, parentRow_mem2101, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2101_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_3_1]
  rfl
theorem row_eq7_5_3_2 : RadiusFivePruning.stateRow7_5_3_2 = ParentOwnership.parentRow2100 := by rfl
theorem patch_mem7_5_3_2 : RadiusFivePruning.patch7_5_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2100, parentRow_mem2100, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2100_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_3_2]
  rfl
theorem row_eq7_5_3_3 : RadiusFivePruning.stateRow7_5_3_3 = ParentOwnership.parentRow2102 := by rfl
theorem patch_mem7_5_3_3 : RadiusFivePruning.patch7_5_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2102, parentRow_mem2102, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2102_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_3_3]
  rfl
theorem row_eq7_5_3_5 : RadiusFivePruning.stateRow7_5_3_5 = ParentOwnership.parentRow0810 := by rfl
theorem patch_mem7_5_3_5 : RadiusFivePruning.patch7_5_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0810, parentRow_mem0810, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0810_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_3_5]
  rfl
theorem row_eq7_5_3_6 : RadiusFivePruning.stateRow7_5_3_6 = ParentOwnership.parentRow0809 := by rfl
theorem patch_mem7_5_3_6 : RadiusFivePruning.patch7_5_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0809, parentRow_mem0809, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0809_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_3_6]
  rfl
theorem row_eq7_5_3_7 : RadiusFivePruning.stateRow7_5_3_7 = ParentOwnership.parentRow2092 := by rfl
theorem patch_mem7_5_3_7 : RadiusFivePruning.patch7_5_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2092, parentRow_mem2092, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2092_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_3_7]
  rfl
theorem row_eq7_5_3_8 : RadiusFivePruning.stateRow7_5_3_8 = ParentOwnership.parentRow2093 := by rfl
theorem patch_mem7_5_3_8 : RadiusFivePruning.patch7_5_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2093, parentRow_mem2093, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2093_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_3_8]
  rfl
theorem row_eq7_5_3_9 : RadiusFivePruning.stateRow7_5_3_9 = ParentOwnership.parentRow2095 := by rfl
theorem patch_mem7_5_3_9 : RadiusFivePruning.patch7_5_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2095, parentRow_mem2095, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2095_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_3_9]
  rfl
theorem row_eq7_5_3_10 : RadiusFivePruning.stateRow7_5_3_10 = ParentOwnership.parentRow2094 := by rfl
theorem patch_mem7_5_3_10 : RadiusFivePruning.patch7_5_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2094, parentRow_mem2094, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2094_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_3_10]
  rfl
theorem row_eq7_5_3_11 : RadiusFivePruning.stateRow7_5_3_11 = ParentOwnership.parentRow0804 := by rfl
theorem patch_mem7_5_3_11 : RadiusFivePruning.patch7_5_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0804, parentRow_mem0804, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0804_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_3_11]
  rfl
theorem chunk_mem7_5_3 : ∀ p ∈ RadiusFivePruning.final7_5_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_5_3, List.forall_mem_cons]
  exact ⟨patch_mem7_5_3_0,⟨patch_mem7_5_3_1,⟨patch_mem7_5_3_2,⟨patch_mem7_5_3_3,⟨patch_mem7_5_3_5,⟨patch_mem7_5_3_6,⟨patch_mem7_5_3_7,⟨patch_mem7_5_3_8,⟨patch_mem7_5_3_9,⟨patch_mem7_5_3_10,⟨patch_mem7_5_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_5_4_1 : RadiusFivePruning.stateRow7_5_4_1 = ParentOwnership.parentRow1524 := by rfl
theorem patch_mem7_5_4_1 : RadiusFivePruning.patch7_5_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1524, parentRow_mem1524, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1524_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_4_1]
  rfl
theorem row_eq7_5_4_2 : RadiusFivePruning.stateRow7_5_4_2 = ParentOwnership.parentRow0814 := by rfl
theorem patch_mem7_5_4_2 : RadiusFivePruning.patch7_5_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0814, parentRow_mem0814, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0814_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_4_2]
  rfl
theorem row_eq7_5_4_3 : RadiusFivePruning.stateRow7_5_4_3 = ParentOwnership.parentRow2096 := by rfl
theorem patch_mem7_5_4_3 : RadiusFivePruning.patch7_5_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2096, parentRow_mem2096, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2096_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_4_3]
  rfl
theorem row_eq7_5_4_4 : RadiusFivePruning.stateRow7_5_4_4 = ParentOwnership.parentRow2097 := by rfl
theorem patch_mem7_5_4_4 : RadiusFivePruning.patch7_5_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2097, parentRow_mem2097, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2097_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_4_4]
  rfl
theorem row_eq7_5_4_5 : RadiusFivePruning.stateRow7_5_4_5 = ParentOwnership.parentRow2098 := by rfl
theorem patch_mem7_5_4_5 : RadiusFivePruning.patch7_5_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2098, parentRow_mem2098, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2098_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_4_5]
  rfl
theorem row_eq7_5_4_8 : RadiusFivePruning.stateRow7_5_4_8 = ParentOwnership.parentRow2089 := by rfl
theorem patch_mem7_5_4_8 : RadiusFivePruning.patch7_5_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2089, parentRow_mem2089, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2089_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_4_8]
  rfl
theorem row_eq7_5_4_10 : RadiusFivePruning.stateRow7_5_4_10 = ParentOwnership.parentRow0803 := by rfl
theorem patch_mem7_5_4_10 : RadiusFivePruning.patch7_5_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0803, parentRow_mem0803, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0803_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_4_10]
  rfl
theorem chunk_mem7_5_4 : ∀ p ∈ RadiusFivePruning.final7_5_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_5_4, List.forall_mem_cons]
  exact ⟨patch_mem7_5_4_1,⟨patch_mem7_5_4_2,⟨patch_mem7_5_4_3,⟨patch_mem7_5_4_4,⟨patch_mem7_5_4_5,⟨patch_mem7_5_4_8,⟨patch_mem7_5_4_10,by simp⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
