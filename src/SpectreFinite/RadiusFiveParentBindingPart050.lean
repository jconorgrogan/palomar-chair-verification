module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock7T5C5
public import SpectreFinite.RadiusFivePruningLiteralBlock7T5C6
public import SpectreFinite.RadiusFivePruningLiteralBlock7T5C7
public import SpectreFinite.RadiusFivePruningLiteralBlock7T5C8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq7_5_5_0 : RadiusFivePruning.stateRow7_5_5_0 = ParentOwnership.parentRow2088 := by rfl
theorem patch_mem7_5_5_0 : RadiusFivePruning.patch7_5_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2088, parentRow_mem2088, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2088_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_5_0]
  rfl
theorem row_eq7_5_5_2 : RadiusFivePruning.stateRow7_5_5_2 = ParentOwnership.parentRow2091 := by rfl
theorem patch_mem7_5_5_2 : RadiusFivePruning.patch7_5_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2091, parentRow_mem2091, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2091_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_5_2]
  rfl
theorem row_eq7_5_5_3 : RadiusFivePruning.stateRow7_5_5_3 = ParentOwnership.parentRow2090 := by rfl
theorem patch_mem7_5_5_3 : RadiusFivePruning.patch7_5_5_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2090, parentRow_mem2090, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2090_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_5_3]
  rfl
theorem row_eq7_5_5_4 : RadiusFivePruning.stateRow7_5_5_4 = ParentOwnership.parentRow0904 := by rfl
theorem patch_mem7_5_5_4 : RadiusFivePruning.patch7_5_5_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0904, parentRow_mem0904, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0904_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_5_4]
  rfl
theorem row_eq7_5_5_5 : RadiusFivePruning.stateRow7_5_5_5 = ParentOwnership.parentRow1032 := by rfl
theorem patch_mem7_5_5_5 : RadiusFivePruning.patch7_5_5_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1032, parentRow_mem1032, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1032_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_5_5]
  rfl
theorem row_eq7_5_5_6 : RadiusFivePruning.stateRow7_5_5_6 = ParentOwnership.parentRow0905 := by rfl
theorem patch_mem7_5_5_6 : RadiusFivePruning.patch7_5_5_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0905, parentRow_mem0905, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0905_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_5_6]
  rfl
theorem row_eq7_5_5_7 : RadiusFivePruning.stateRow7_5_5_7 = ParentOwnership.parentRow0909 := by rfl
theorem patch_mem7_5_5_7 : RadiusFivePruning.patch7_5_5_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0909, parentRow_mem0909, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0909_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_5_7]
  rfl
theorem row_eq7_5_5_8 : RadiusFivePruning.stateRow7_5_5_8 = ParentOwnership.parentRow1030 := by rfl
theorem patch_mem7_5_5_8 : RadiusFivePruning.patch7_5_5_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1030, parentRow_mem1030, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1030_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_5_8]
  rfl
theorem row_eq7_5_5_9 : RadiusFivePruning.stateRow7_5_5_9 = ParentOwnership.parentRow1031 := by rfl
theorem patch_mem7_5_5_9 : RadiusFivePruning.patch7_5_5_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1031, parentRow_mem1031, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1031_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_5_9]
  rfl
theorem row_eq7_5_5_10 : RadiusFivePruning.stateRow7_5_5_10 = ParentOwnership.parentRow0908 := by rfl
theorem patch_mem7_5_5_10 : RadiusFivePruning.patch7_5_5_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0908, parentRow_mem0908, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0908_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_5_10]
  rfl
theorem row_eq7_5_5_11 : RadiusFivePruning.stateRow7_5_5_11 = ParentOwnership.parentRow0906 := by rfl
theorem patch_mem7_5_5_11 : RadiusFivePruning.patch7_5_5_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0906, parentRow_mem0906, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0906_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_5_11]
  rfl
theorem chunk_mem7_5_5 : ∀ p ∈ RadiusFivePruning.final7_5_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_5_5, List.forall_mem_cons]
  exact ⟨patch_mem7_5_5_0,⟨patch_mem7_5_5_2,⟨patch_mem7_5_5_3,⟨patch_mem7_5_5_4,⟨patch_mem7_5_5_5,⟨patch_mem7_5_5_6,⟨patch_mem7_5_5_7,⟨patch_mem7_5_5_8,⟨patch_mem7_5_5_9,⟨patch_mem7_5_5_10,⟨patch_mem7_5_5_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_5_6_0 : RadiusFivePruning.stateRow7_5_6_0 = ParentOwnership.parentRow1033 := by rfl
theorem patch_mem7_5_6_0 : RadiusFivePruning.patch7_5_6_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1033, parentRow_mem1033, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1033_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_6_0]
  rfl
theorem row_eq7_5_6_1 : RadiusFivePruning.stateRow7_5_6_1 = ParentOwnership.parentRow0907 := by rfl
theorem patch_mem7_5_6_1 : RadiusFivePruning.patch7_5_6_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0907, parentRow_mem0907, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0907_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_6_1]
  rfl
theorem row_eq7_5_6_2 : RadiusFivePruning.stateRow7_5_6_2 = ParentOwnership.parentRow0910 := by rfl
theorem patch_mem7_5_6_2 : RadiusFivePruning.patch7_5_6_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0910, parentRow_mem0910, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0910_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_6_2]
  rfl
theorem row_eq7_5_6_4 : RadiusFivePruning.stateRow7_5_6_4 = ParentOwnership.parentRow1539 := by rfl
theorem patch_mem7_5_6_4 : RadiusFivePruning.patch7_5_6_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1539, parentRow_mem1539, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1539_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_6_4]
  rfl
theorem row_eq7_5_6_6 : RadiusFivePruning.stateRow7_5_6_6 = ParentOwnership.parentRow0822 := by rfl
theorem patch_mem7_5_6_6 : RadiusFivePruning.patch7_5_6_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0822, parentRow_mem0822, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0822_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_6_6]
  rfl
theorem row_eq7_5_6_7 : RadiusFivePruning.stateRow7_5_6_7 = ParentOwnership.parentRow2109 := by rfl
theorem patch_mem7_5_6_7 : RadiusFivePruning.patch7_5_6_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2109, parentRow_mem2109, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2109_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_6_7]
  rfl
theorem row_eq7_5_6_9 : RadiusFivePruning.stateRow7_5_6_9 = ParentOwnership.parentRow2107 := by rfl
theorem patch_mem7_5_6_9 : RadiusFivePruning.patch7_5_6_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2107, parentRow_mem2107, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2107_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_6_9]
  rfl
theorem row_eq7_5_6_10 : RadiusFivePruning.stateRow7_5_6_10 = ParentOwnership.parentRow2110 := by rfl
theorem patch_mem7_5_6_10 : RadiusFivePruning.patch7_5_6_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2110, parentRow_mem2110, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2110_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_6_10]
  rfl
theorem row_eq7_5_6_11 : RadiusFivePruning.stateRow7_5_6_11 = ParentOwnership.parentRow2108 := by rfl
theorem patch_mem7_5_6_11 : RadiusFivePruning.patch7_5_6_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2108, parentRow_mem2108, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2108_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_6_11]
  rfl
theorem chunk_mem7_5_6 : ∀ p ∈ RadiusFivePruning.final7_5_6, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_5_6, List.forall_mem_cons]
  exact ⟨patch_mem7_5_6_0,⟨patch_mem7_5_6_1,⟨patch_mem7_5_6_2,⟨patch_mem7_5_6_4,⟨patch_mem7_5_6_6,⟨patch_mem7_5_6_7,⟨patch_mem7_5_6_9,⟨patch_mem7_5_6_10,⟨patch_mem7_5_6_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_5_7_0 : RadiusFivePruning.stateRow7_5_7_0 = ParentOwnership.parentRow2111 := by rfl
theorem patch_mem7_5_7_0 : RadiusFivePruning.patch7_5_7_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2111, parentRow_mem2111, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2111_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_7_0]
  rfl
theorem row_eq7_5_7_1 : RadiusFivePruning.stateRow7_5_7_1 = ParentOwnership.parentRow0373 := by rfl
theorem patch_mem7_5_7_1 : RadiusFivePruning.patch7_5_7_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0373, parentRow_mem0373, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0373_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_7_1]
  rfl
theorem row_eq7_5_7_2 : RadiusFivePruning.stateRow7_5_7_2 = ParentOwnership.parentRow0597 := by rfl
theorem patch_mem7_5_7_2 : RadiusFivePruning.patch7_5_7_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0597, parentRow_mem0597, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0597_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_7_2]
  rfl
theorem row_eq7_5_7_3 : RadiusFivePruning.stateRow7_5_7_3 = ParentOwnership.parentRow0374 := by rfl
theorem patch_mem7_5_7_3 : RadiusFivePruning.patch7_5_7_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0374, parentRow_mem0374, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0374_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_7_3]
  rfl
theorem row_eq7_5_7_4 : RadiusFivePruning.stateRow7_5_7_4 = ParentOwnership.parentRow0598 := by rfl
theorem patch_mem7_5_7_4 : RadiusFivePruning.patch7_5_7_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0598, parentRow_mem0598, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0598_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_7_4]
  rfl
theorem row_eq7_5_7_5 : RadiusFivePruning.stateRow7_5_7_5 = ParentOwnership.parentRow0900 := by rfl
theorem patch_mem7_5_7_5 : RadiusFivePruning.patch7_5_7_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0900, parentRow_mem0900, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0900_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_7_5]
  rfl
theorem row_eq7_5_7_6 : RadiusFivePruning.stateRow7_5_7_6 = ParentOwnership.parentRow0899 := by rfl
theorem patch_mem7_5_7_6 : RadiusFivePruning.patch7_5_7_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0899, parentRow_mem0899, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0899_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_7_6]
  rfl
theorem row_eq7_5_7_11 : RadiusFivePruning.stateRow7_5_7_11 = ParentOwnership.parentRow0903 := by rfl
theorem patch_mem7_5_7_11 : RadiusFivePruning.patch7_5_7_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0903, parentRow_mem0903, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0903_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_7_11]
  rfl
theorem chunk_mem7_5_7 : ∀ p ∈ RadiusFivePruning.final7_5_7, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_5_7, List.forall_mem_cons]
  exact ⟨patch_mem7_5_7_0,⟨patch_mem7_5_7_1,⟨patch_mem7_5_7_2,⟨patch_mem7_5_7_3,⟨patch_mem7_5_7_4,⟨patch_mem7_5_7_5,⟨patch_mem7_5_7_6,⟨patch_mem7_5_7_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_5_8_0 : RadiusFivePruning.stateRow7_5_8_0 = ParentOwnership.parentRow0901 := by rfl
theorem patch_mem7_5_8_0 : RadiusFivePruning.patch7_5_8_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0901, parentRow_mem0901, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0901_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_8_0]
  rfl
theorem row_eq7_5_8_1 : RadiusFivePruning.stateRow7_5_8_1 = ParentOwnership.parentRow1028 := by rfl
theorem patch_mem7_5_8_1 : RadiusFivePruning.patch7_5_8_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1028, parentRow_mem1028, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1028_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_8_1]
  rfl
theorem row_eq7_5_8_2 : RadiusFivePruning.stateRow7_5_8_2 = ParentOwnership.parentRow1029 := by rfl
theorem patch_mem7_5_8_2 : RadiusFivePruning.patch7_5_8_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1029, parentRow_mem1029, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1029_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_8_2]
  rfl
theorem row_eq7_5_8_3 : RadiusFivePruning.stateRow7_5_8_3 = ParentOwnership.parentRow0902 := by rfl
theorem patch_mem7_5_8_3 : RadiusFivePruning.patch7_5_8_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0902, parentRow_mem0902, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0902_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_8_3]
  rfl
theorem row_eq7_5_8_5 : RadiusFivePruning.stateRow7_5_8_5 = ParentOwnership.parentRow0371 := by rfl
theorem patch_mem7_5_8_5 : RadiusFivePruning.patch7_5_8_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0371, parentRow_mem0371, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0371_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_8_5]
  rfl
theorem row_eq7_5_8_7 : RadiusFivePruning.stateRow7_5_8_7 = ParentOwnership.parentRow0370 := by rfl
theorem patch_mem7_5_8_7 : RadiusFivePruning.patch7_5_8_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0370, parentRow_mem0370, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0370_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_8_7]
  rfl
theorem row_eq7_5_8_8 : RadiusFivePruning.stateRow7_5_8_8 = ParentOwnership.parentRow0596 := by rfl
theorem patch_mem7_5_8_8 : RadiusFivePruning.patch7_5_8_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0596, parentRow_mem0596, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0596_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_8_8]
  rfl
theorem row_eq7_5_8_9 : RadiusFivePruning.stateRow7_5_8_9 = ParentOwnership.parentRow1469 := by rfl
theorem patch_mem7_5_8_9 : RadiusFivePruning.patch7_5_8_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1469, parentRow_mem1469, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1469_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_5_8_9]
  rfl
theorem chunk_mem7_5_8 : ∀ p ∈ RadiusFivePruning.final7_5_8, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_5_8, List.forall_mem_cons]
  exact ⟨patch_mem7_5_8_0,⟨patch_mem7_5_8_1,⟨patch_mem7_5_8_2,⟨patch_mem7_5_8_3,⟨patch_mem7_5_8_5,⟨patch_mem7_5_8_7,⟨patch_mem7_5_8_8,⟨patch_mem7_5_8_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
