module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock5T2C2
public import SpectreFinite.RadiusFivePruningLiteralBlock5T3C0
public import SpectreFinite.RadiusFivePruningLiteralBlock5T3C1
public import SpectreFinite.RadiusFivePruningLiteralBlock5T3C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq5_2_2_0 : RadiusFivePruning.stateRow5_2_2_0 = ParentOwnership.parentRow1152 := by rfl
theorem patch_mem5_2_2_0 : RadiusFivePruning.patch5_2_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1152, parentRow_mem1152, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1152_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_2_0]
  rfl
theorem row_eq5_2_2_1 : RadiusFivePruning.stateRow5_2_2_1 = ParentOwnership.parentRow1144 := by rfl
theorem patch_mem5_2_2_1 : RadiusFivePruning.patch5_2_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1144, parentRow_mem1144, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1144_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_2_1]
  rfl
theorem row_eq5_2_2_2 : RadiusFivePruning.stateRow5_2_2_2 = ParentOwnership.parentRow0412 := by rfl
theorem patch_mem5_2_2_2 : RadiusFivePruning.patch5_2_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0412, parentRow_mem0412, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0412_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_2_2]
  rfl
theorem row_eq5_2_2_3 : RadiusFivePruning.stateRow5_2_2_3 = ParentOwnership.parentRow0413 := by rfl
theorem patch_mem5_2_2_3 : RadiusFivePruning.patch5_2_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0413, parentRow_mem0413, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0413_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_2_3]
  rfl
theorem row_eq5_2_2_4 : RadiusFivePruning.stateRow5_2_2_4 = ParentOwnership.parentRow0399 := by rfl
theorem patch_mem5_2_2_4 : RadiusFivePruning.patch5_2_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0399, parentRow_mem0399, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0399_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_2_4]
  rfl
theorem row_eq5_2_2_5 : RadiusFivePruning.stateRow5_2_2_5 = ParentOwnership.parentRow0411 := by rfl
theorem patch_mem5_2_2_5 : RadiusFivePruning.patch5_2_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0411, parentRow_mem0411, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0411_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_2_5]
  rfl
theorem row_eq5_2_2_6 : RadiusFivePruning.stateRow5_2_2_6 = ParentOwnership.parentRow0416 := by rfl
theorem patch_mem5_2_2_6 : RadiusFivePruning.patch5_2_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0416, parentRow_mem0416, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0416_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_2_6]
  rfl
theorem row_eq5_2_2_7 : RadiusFivePruning.stateRow5_2_2_7 = ParentOwnership.parentRow0417 := by rfl
theorem patch_mem5_2_2_7 : RadiusFivePruning.patch5_2_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0417, parentRow_mem0417, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0417_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_2_7]
  rfl
theorem row_eq5_2_2_8 : RadiusFivePruning.stateRow5_2_2_8 = ParentOwnership.parentRow0404 := by rfl
theorem patch_mem5_2_2_8 : RadiusFivePruning.patch5_2_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0404, parentRow_mem0404, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0404_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_2_8]
  rfl
theorem row_eq5_2_2_9 : RadiusFivePruning.stateRow5_2_2_9 = ParentOwnership.parentRow0415 := by rfl
theorem patch_mem5_2_2_9 : RadiusFivePruning.patch5_2_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0415, parentRow_mem0415, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0415_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_2_9]
  rfl
theorem row_eq5_2_2_10 : RadiusFivePruning.stateRow5_2_2_10 = ParentOwnership.parentRow0414 := by rfl
theorem patch_mem5_2_2_10 : RadiusFivePruning.patch5_2_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0414, parentRow_mem0414, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0414_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_2_10]
  rfl
theorem chunk_mem5_2_2 : ∀ p ∈ RadiusFivePruning.final5_2_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_2_2, List.forall_mem_cons]
  exact ⟨patch_mem5_2_2_0,⟨patch_mem5_2_2_1,⟨patch_mem5_2_2_2,⟨patch_mem5_2_2_3,⟨patch_mem5_2_2_4,⟨patch_mem5_2_2_5,⟨patch_mem5_2_2_6,⟨patch_mem5_2_2_7,⟨patch_mem5_2_2_8,⟨patch_mem5_2_2_9,⟨patch_mem5_2_2_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq5_3_0_2 : RadiusFivePruning.stateRow5_3_0_2 = ParentOwnership.parentRow1610 := by rfl
theorem patch_mem5_3_0_2 : RadiusFivePruning.patch5_3_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1610, parentRow_mem1610, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1610_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_0_2]
  rfl
theorem row_eq5_3_0_3 : RadiusFivePruning.stateRow5_3_0_3 = ParentOwnership.parentRow1609 := by rfl
theorem patch_mem5_3_0_3 : RadiusFivePruning.patch5_3_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1609, parentRow_mem1609, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1609_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_0_3]
  rfl
theorem row_eq5_3_0_4 : RadiusFivePruning.stateRow5_3_0_4 = ParentOwnership.parentRow1608 := by rfl
theorem patch_mem5_3_0_4 : RadiusFivePruning.patch5_3_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1608, parentRow_mem1608, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1608_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_0_4]
  rfl
theorem row_eq5_3_0_6 : RadiusFivePruning.stateRow5_3_0_6 = ParentOwnership.parentRow1612 := by rfl
theorem patch_mem5_3_0_6 : RadiusFivePruning.patch5_3_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1612, parentRow_mem1612, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1612_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_0_6]
  rfl
theorem row_eq5_3_0_7 : RadiusFivePruning.stateRow5_3_0_7 = ParentOwnership.parentRow1611 := by rfl
theorem patch_mem5_3_0_7 : RadiusFivePruning.patch5_3_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1611, parentRow_mem1611, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1611_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_0_7]
  rfl
theorem row_eq5_3_0_9 : RadiusFivePruning.stateRow5_3_0_9 = ParentOwnership.parentRow0487 := by rfl
theorem patch_mem5_3_0_9 : RadiusFivePruning.patch5_3_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0487, parentRow_mem0487, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0487_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_0_9]
  rfl
theorem row_eq5_3_0_10 : RadiusFivePruning.stateRow5_3_0_10 = ParentOwnership.parentRow0058 := by rfl
theorem patch_mem5_3_0_10 : RadiusFivePruning.patch5_3_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0058, parentRow_mem0058, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0058_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_0_10]
  rfl
theorem row_eq5_3_0_11 : RadiusFivePruning.stateRow5_3_0_11 = ParentOwnership.parentRow0493 := by rfl
theorem patch_mem5_3_0_11 : RadiusFivePruning.patch5_3_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0493, parentRow_mem0493, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0493_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_0_11]
  rfl
theorem chunk_mem5_3_0 : ∀ p ∈ RadiusFivePruning.final5_3_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_3_0, List.forall_mem_cons]
  exact ⟨patch_mem5_3_0_2,⟨patch_mem5_3_0_3,⟨patch_mem5_3_0_4,⟨patch_mem5_3_0_6,⟨patch_mem5_3_0_7,⟨patch_mem5_3_0_9,⟨patch_mem5_3_0_10,⟨patch_mem5_3_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq5_3_1_0 : RadiusFivePruning.stateRow5_3_1_0 = ParentOwnership.parentRow1665 := by rfl
theorem patch_mem5_3_1_0 : RadiusFivePruning.patch5_3_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1665, parentRow_mem1665, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1665_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_1_0]
  rfl
theorem row_eq5_3_1_1 : RadiusFivePruning.stateRow5_3_1_1 = ParentOwnership.parentRow0508 := by rfl
theorem patch_mem5_3_1_1 : RadiusFivePruning.patch5_3_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0508, parentRow_mem0508, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0508_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_1_1]
  rfl
theorem row_eq5_3_1_3 : RadiusFivePruning.stateRow5_3_1_3 = ParentOwnership.parentRow0501 := by rfl
theorem patch_mem5_3_1_3 : RadiusFivePruning.patch5_3_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0501, parentRow_mem0501, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0501_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_1_3]
  rfl
theorem row_eq5_3_1_4 : RadiusFivePruning.stateRow5_3_1_4 = ParentOwnership.parentRow0486 := by rfl
theorem patch_mem5_3_1_4 : RadiusFivePruning.patch5_3_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0486, parentRow_mem0486, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0486_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_1_4]
  rfl
theorem row_eq5_3_1_7 : RadiusFivePruning.stateRow5_3_1_7 = ParentOwnership.parentRow1669 := by rfl
theorem patch_mem5_3_1_7 : RadiusFivePruning.patch5_3_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1669, parentRow_mem1669, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1669_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_1_7]
  rfl
theorem row_eq5_3_1_8 : RadiusFivePruning.stateRow5_3_1_8 = ParentOwnership.parentRow0490 := by rfl
theorem patch_mem5_3_1_8 : RadiusFivePruning.patch5_3_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0490, parentRow_mem0490, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0490_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_1_8]
  rfl
theorem row_eq5_3_1_9 : RadiusFivePruning.stateRow5_3_1_9 = ParentOwnership.parentRow0494 := by rfl
theorem patch_mem5_3_1_9 : RadiusFivePruning.patch5_3_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0494, parentRow_mem0494, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0494_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_1_9]
  rfl
theorem row_eq5_3_1_11 : RadiusFivePruning.stateRow5_3_1_11 = ParentOwnership.parentRow1666 := by rfl
theorem patch_mem5_3_1_11 : RadiusFivePruning.patch5_3_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1666, parentRow_mem1666, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1666_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_1_11]
  rfl
theorem chunk_mem5_3_1 : ∀ p ∈ RadiusFivePruning.final5_3_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_3_1, List.forall_mem_cons]
  exact ⟨patch_mem5_3_1_0,⟨patch_mem5_3_1_1,⟨patch_mem5_3_1_3,⟨patch_mem5_3_1_4,⟨patch_mem5_3_1_7,⟨patch_mem5_3_1_8,⟨patch_mem5_3_1_9,⟨patch_mem5_3_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq5_3_2_0 : RadiusFivePruning.stateRow5_3_2_0 = ParentOwnership.parentRow0057 := by rfl
theorem patch_mem5_3_2_0 : RadiusFivePruning.patch5_3_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0057, parentRow_mem0057, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0057_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_2_0]
  rfl
theorem row_eq5_3_2_1 : RadiusFivePruning.stateRow5_3_2_1 = ParentOwnership.parentRow0492 := by rfl
theorem patch_mem5_3_2_1 : RadiusFivePruning.patch5_3_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0492, parentRow_mem0492, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0492_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_2_1]
  rfl
theorem row_eq5_3_2_2 : RadiusFivePruning.stateRow5_3_2_2 = ParentOwnership.parentRow0503 := by rfl
theorem patch_mem5_3_2_2 : RadiusFivePruning.patch5_3_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0503, parentRow_mem0503, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0503_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_2_2]
  rfl
theorem row_eq5_3_2_3 : RadiusFivePruning.stateRow5_3_2_3 = ParentOwnership.parentRow0504 := by rfl
theorem patch_mem5_3_2_3 : RadiusFivePruning.patch5_3_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0504, parentRow_mem0504, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0504_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_2_3]
  rfl
theorem row_eq5_3_2_4 : RadiusFivePruning.stateRow5_3_2_4 = ParentOwnership.parentRow1667 := by rfl
theorem patch_mem5_3_2_4 : RadiusFivePruning.patch5_3_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1667, parentRow_mem1667, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1667_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_2_4]
  rfl
theorem row_eq5_3_2_5 : RadiusFivePruning.stateRow5_3_2_5 = ParentOwnership.parentRow0488 := by rfl
theorem patch_mem5_3_2_5 : RadiusFivePruning.patch5_3_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0488, parentRow_mem0488, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0488_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_2_5]
  rfl
theorem row_eq5_3_2_6 : RadiusFivePruning.stateRow5_3_2_6 = ParentOwnership.parentRow0505 := by rfl
theorem patch_mem5_3_2_6 : RadiusFivePruning.patch5_3_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0505, parentRow_mem0505, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0505_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_2_6]
  rfl
theorem row_eq5_3_2_7 : RadiusFivePruning.stateRow5_3_2_7 = ParentOwnership.parentRow0506 := by rfl
theorem patch_mem5_3_2_7 : RadiusFivePruning.patch5_3_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0506, parentRow_mem0506, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0506_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_2_7]
  rfl
theorem row_eq5_3_2_8 : RadiusFivePruning.stateRow5_3_2_8 = ParentOwnership.parentRow1668 := by rfl
theorem patch_mem5_3_2_8 : RadiusFivePruning.patch5_3_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1668, parentRow_mem1668, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1668_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_2_8]
  rfl
theorem row_eq5_3_2_9 : RadiusFivePruning.stateRow5_3_2_9 = ParentOwnership.parentRow0489 := by rfl
theorem patch_mem5_3_2_9 : RadiusFivePruning.patch5_3_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0489, parentRow_mem0489, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0489_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_2_9]
  rfl
theorem row_eq5_3_2_10 : RadiusFivePruning.stateRow5_3_2_10 = ParentOwnership.parentRow0507 := by rfl
theorem patch_mem5_3_2_10 : RadiusFivePruning.patch5_3_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0507, parentRow_mem0507, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0507_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_3_2_10]
  rfl
theorem chunk_mem5_3_2 : ∀ p ∈ RadiusFivePruning.final5_3_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_3_2, List.forall_mem_cons]
  exact ⟨patch_mem5_3_2_0,⟨patch_mem5_3_2_1,⟨patch_mem5_3_2_2,⟨patch_mem5_3_2_3,⟨patch_mem5_3_2_4,⟨patch_mem5_3_2_5,⟨patch_mem5_3_2_6,⟨patch_mem5_3_2_7,⟨patch_mem5_3_2_8,⟨patch_mem5_3_2_9,⟨patch_mem5_3_2_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
