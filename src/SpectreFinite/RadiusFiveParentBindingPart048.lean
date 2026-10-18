module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock7T4C6
public import SpectreFinite.RadiusFivePruningLiteralBlock7T4C7
public import SpectreFinite.RadiusFivePruningLiteralBlock7T4C8
public import SpectreFinite.RadiusFivePruningLiteralBlock7T5C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq7_4_6_0 : RadiusFivePruning.stateRow7_4_6_0 = ParentOwnership.parentRow1738 := by rfl
theorem patch_mem7_4_6_0 : RadiusFivePruning.patch7_4_6_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1738, parentRow_mem1738, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1738_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_6_0]
  rfl
theorem row_eq7_4_6_1 : RadiusFivePruning.stateRow7_4_6_1 = ParentOwnership.parentRow1750 := by rfl
theorem patch_mem7_4_6_1 : RadiusFivePruning.patch7_4_6_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1750, parentRow_mem1750, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1750_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_6_1]
  rfl
theorem row_eq7_4_6_2 : RadiusFivePruning.stateRow7_4_6_2 = ParentOwnership.parentRow1729 := by rfl
theorem patch_mem7_4_6_2 : RadiusFivePruning.patch7_4_6_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1729, parentRow_mem1729, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1729_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_6_2]
  rfl
theorem row_eq7_4_6_4 : RadiusFivePruning.stateRow7_4_6_4 = ParentOwnership.parentRow1858 := by rfl
theorem patch_mem7_4_6_4 : RadiusFivePruning.patch7_4_6_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1858, parentRow_mem1858, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1858_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_6_4]
  rfl
theorem row_eq7_4_6_6 : RadiusFivePruning.stateRow7_4_6_6 = ParentOwnership.parentRow1852 := by rfl
theorem patch_mem7_4_6_6 : RadiusFivePruning.patch7_4_6_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1852, parentRow_mem1852, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1852_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_6_6]
  rfl
theorem row_eq7_4_6_7 : RadiusFivePruning.stateRow7_4_6_7 = ParentOwnership.parentRow0647 := by rfl
theorem patch_mem7_4_6_7 : RadiusFivePruning.patch7_4_6_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0647, parentRow_mem0647, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0647_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_6_7]
  rfl
theorem row_eq7_4_6_9 : RadiusFivePruning.stateRow7_4_6_9 = ParentOwnership.parentRow0648 := by rfl
theorem patch_mem7_4_6_9 : RadiusFivePruning.patch7_4_6_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0648, parentRow_mem0648, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0648_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_6_9]
  rfl
theorem row_eq7_4_6_10 : RadiusFivePruning.stateRow7_4_6_10 = ParentOwnership.parentRow1721 := by rfl
theorem patch_mem7_4_6_10 : RadiusFivePruning.patch7_4_6_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1721, parentRow_mem1721, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1721_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_6_10]
  rfl
theorem row_eq7_4_6_11 : RadiusFivePruning.stateRow7_4_6_11 = ParentOwnership.parentRow0651 := by rfl
theorem patch_mem7_4_6_11 : RadiusFivePruning.patch7_4_6_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0651, parentRow_mem0651, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0651_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_6_11]
  rfl
theorem chunk_mem7_4_6 : ∀ p ∈ RadiusFivePruning.final7_4_6, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_4_6, List.forall_mem_cons]
  exact ⟨patch_mem7_4_6_0,⟨patch_mem7_4_6_1,⟨patch_mem7_4_6_2,⟨patch_mem7_4_6_4,⟨patch_mem7_4_6_6,⟨patch_mem7_4_6_7,⟨patch_mem7_4_6_9,⟨patch_mem7_4_6_10,⟨patch_mem7_4_6_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_4_7_0 : RadiusFivePruning.stateRow7_4_7_0 = ParentOwnership.parentRow1724 := by rfl
theorem patch_mem7_4_7_0 : RadiusFivePruning.patch7_4_7_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1724, parentRow_mem1724, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1724_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_7_0]
  rfl
theorem row_eq7_4_7_1 : RadiusFivePruning.stateRow7_4_7_1 = ParentOwnership.parentRow0656 := by rfl
theorem patch_mem7_4_7_1 : RadiusFivePruning.patch7_4_7_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0656, parentRow_mem0656, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0656_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_7_1]
  rfl
theorem row_eq7_4_7_2 : RadiusFivePruning.stateRow7_4_7_2 = ParentOwnership.parentRow1755 := by rfl
theorem patch_mem7_4_7_2 : RadiusFivePruning.patch7_4_7_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1755, parentRow_mem1755, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1755_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_7_2]
  rfl
theorem row_eq7_4_7_3 : RadiusFivePruning.stateRow7_4_7_3 = ParentOwnership.parentRow0657 := by rfl
theorem patch_mem7_4_7_3 : RadiusFivePruning.patch7_4_7_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0657, parentRow_mem0657, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0657_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_7_3]
  rfl
theorem row_eq7_4_7_4 : RadiusFivePruning.stateRow7_4_7_4 = ParentOwnership.parentRow1756 := by rfl
theorem patch_mem7_4_7_4 : RadiusFivePruning.patch7_4_7_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1756, parentRow_mem1756, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1756_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_7_4]
  rfl
theorem row_eq7_4_7_5 : RadiusFivePruning.stateRow7_4_7_5 = ParentOwnership.parentRow1752 := by rfl
theorem patch_mem7_4_7_5 : RadiusFivePruning.patch7_4_7_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1752, parentRow_mem1752, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1752_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_7_5]
  rfl
theorem row_eq7_4_7_6 : RadiusFivePruning.stateRow7_4_7_6 = ParentOwnership.parentRow1751 := by rfl
theorem patch_mem7_4_7_6 : RadiusFivePruning.patch7_4_7_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1751, parentRow_mem1751, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1751_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_7_6]
  rfl
theorem row_eq7_4_7_11 : RadiusFivePruning.stateRow7_4_7_11 = ParentOwnership.parentRow1730 := by rfl
theorem patch_mem7_4_7_11 : RadiusFivePruning.patch7_4_7_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1730, parentRow_mem1730, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1730_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_7_11]
  rfl
theorem chunk_mem7_4_7 : ∀ p ∈ RadiusFivePruning.final7_4_7, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_4_7, List.forall_mem_cons]
  exact ⟨patch_mem7_4_7_0,⟨patch_mem7_4_7_1,⟨patch_mem7_4_7_2,⟨patch_mem7_4_7_3,⟨patch_mem7_4_7_4,⟨patch_mem7_4_7_5,⟨patch_mem7_4_7_6,⟨patch_mem7_4_7_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_4_8_0 : RadiusFivePruning.stateRow7_4_8_0 = ParentOwnership.parentRow1736 := by rfl
theorem patch_mem7_4_8_0 : RadiusFivePruning.patch7_4_8_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1736, parentRow_mem1736, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1736_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_8_0]
  rfl
theorem row_eq7_4_8_1 : RadiusFivePruning.stateRow7_4_8_1 = ParentOwnership.parentRow1742 := by rfl
theorem patch_mem7_4_8_1 : RadiusFivePruning.patch7_4_8_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1742, parentRow_mem1742, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1742_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_8_1]
  rfl
theorem row_eq7_4_8_2 : RadiusFivePruning.stateRow7_4_8_2 = ParentOwnership.parentRow1744 := by rfl
theorem patch_mem7_4_8_2 : RadiusFivePruning.patch7_4_8_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1744, parentRow_mem1744, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1744_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_8_2]
  rfl
theorem row_eq7_4_8_3 : RadiusFivePruning.stateRow7_4_8_3 = ParentOwnership.parentRow1735 := by rfl
theorem patch_mem7_4_8_3 : RadiusFivePruning.patch7_4_8_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1735, parentRow_mem1735, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1735_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_8_3]
  rfl
theorem row_eq7_4_8_5 : RadiusFivePruning.stateRow7_4_8_5 = ParentOwnership.parentRow0658 := by rfl
theorem patch_mem7_4_8_5 : RadiusFivePruning.patch7_4_8_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0658, parentRow_mem0658, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0658_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_8_5]
  rfl
theorem row_eq7_4_8_7 : RadiusFivePruning.stateRow7_4_8_7 = ParentOwnership.parentRow0655 := by rfl
theorem patch_mem7_4_8_7 : RadiusFivePruning.patch7_4_8_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0655, parentRow_mem0655, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0655_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_8_7]
  rfl
theorem row_eq7_4_8_8 : RadiusFivePruning.stateRow7_4_8_8 = ParentOwnership.parentRow1757 := by rfl
theorem patch_mem7_4_8_8 : RadiusFivePruning.patch7_4_8_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1757, parentRow_mem1757, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1757_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_8_8]
  rfl
theorem row_eq7_4_8_9 : RadiusFivePruning.stateRow7_4_8_9 = ParentOwnership.parentRow1760 := by rfl
theorem patch_mem7_4_8_9 : RadiusFivePruning.patch7_4_8_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1760, parentRow_mem1760, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1760_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_8_9]
  rfl
theorem chunk_mem7_4_8 : ∀ p ∈ RadiusFivePruning.final7_4_8, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_4_8, List.forall_mem_cons]
  exact ⟨patch_mem7_4_8_0,⟨patch_mem7_4_8_1,⟨patch_mem7_4_8_2,⟨patch_mem7_4_8_3,⟨patch_mem7_4_8_5,⟨patch_mem7_4_8_7,⟨patch_mem7_4_8_8,⟨patch_mem7_4_8_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_5_0_1 : RadiusFivePruning.stateRow7_5_0_1 = ParentOwnership.parentRow1533 := by rfl
theorem patch_mem7_5_0_1 : RadiusFivePruning.patch7_5_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1533, parentRow_mem1533, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1533_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_0_1]
  rfl
theorem row_eq7_5_0_2 : RadiusFivePruning.stateRow7_5_0_2 = ParentOwnership.parentRow1536 := by rfl
theorem patch_mem7_5_0_2 : RadiusFivePruning.patch7_5_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1536, parentRow_mem1536, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1536_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_0_2]
  rfl
theorem row_eq7_5_0_3 : RadiusFivePruning.stateRow7_5_0_3 = ParentOwnership.parentRow0819 := by rfl
theorem patch_mem7_5_0_3 : RadiusFivePruning.patch7_5_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0819, parentRow_mem0819, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0819_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_0_3]
  rfl
theorem row_eq7_5_0_4 : RadiusFivePruning.stateRow7_5_0_4 = ParentOwnership.parentRow2103 := by rfl
theorem patch_mem7_5_0_4 : RadiusFivePruning.patch7_5_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2103, parentRow_mem2103, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2103_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_0_4]
  rfl
theorem row_eq7_5_0_5 : RadiusFivePruning.stateRow7_5_0_5 = ParentOwnership.parentRow2105 := by rfl
theorem patch_mem7_5_0_5 : RadiusFivePruning.patch7_5_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2105, parentRow_mem2105, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2105_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_0_5]
  rfl
theorem row_eq7_5_0_6 : RadiusFivePruning.stateRow7_5_0_6 = ParentOwnership.parentRow2104 := by rfl
theorem patch_mem7_5_0_6 : RadiusFivePruning.patch7_5_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2104, parentRow_mem2104, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2104_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_0_6]
  rfl
theorem row_eq7_5_0_7 : RadiusFivePruning.stateRow7_5_0_7 = ParentOwnership.parentRow2106 := by rfl
theorem patch_mem7_5_0_7 : RadiusFivePruning.patch7_5_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2106, parentRow_mem2106, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2106_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_0_7]
  rfl
theorem row_eq7_5_0_8 : RadiusFivePruning.stateRow7_5_0_8 = ParentOwnership.parentRow1579 := by rfl
theorem patch_mem7_5_0_8 : RadiusFivePruning.patch7_5_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1579, parentRow_mem1579, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1579_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_0_8]
  rfl
theorem row_eq7_5_0_11 : RadiusFivePruning.stateRow7_5_0_11 = ParentOwnership.parentRow1534 := by rfl
theorem patch_mem7_5_0_11 : RadiusFivePruning.patch7_5_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1534, parentRow_mem1534, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1534_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_0_11]
  rfl
theorem chunk_mem7_5_0 : ∀ p ∈ RadiusFivePruning.final7_5_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_5_0, List.forall_mem_cons]
  exact ⟨patch_mem7_5_0_1,⟨patch_mem7_5_0_2,⟨patch_mem7_5_0_3,⟨patch_mem7_5_0_4,⟨patch_mem7_5_0_5,⟨patch_mem7_5_0_6,⟨patch_mem7_5_0_7,⟨patch_mem7_5_0_8,⟨patch_mem7_5_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
