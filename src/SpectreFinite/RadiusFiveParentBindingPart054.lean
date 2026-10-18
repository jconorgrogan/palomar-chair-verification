module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock8T2C0
public import SpectreFinite.RadiusFivePruningLiteralBlock8T2C1
public import SpectreFinite.RadiusFivePruningLiteralBlock8T2C2
public import SpectreFinite.RadiusFivePruningLiteralBlock8T2C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq8_2_0_1 : RadiusFivePruning.stateRow8_2_0_1 = ParentOwnership.parentRow0188 := by rfl
theorem patch_mem8_2_0_1 : RadiusFivePruning.patch8_2_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0188, parentRow_mem0188, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0188_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_0_1]
  rfl
theorem row_eq8_2_0_3 : RadiusFivePruning.stateRow8_2_0_3 = ParentOwnership.parentRow0186 := by rfl
theorem patch_mem8_2_0_3 : RadiusFivePruning.patch8_2_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0186, parentRow_mem0186, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0186_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_0_3]
  rfl
theorem row_eq8_2_0_4 : RadiusFivePruning.stateRow8_2_0_4 = ParentOwnership.parentRow0189 := by rfl
theorem patch_mem8_2_0_4 : RadiusFivePruning.patch8_2_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0189, parentRow_mem0189, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0189_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_0_4]
  rfl
theorem row_eq8_2_0_5 : RadiusFivePruning.stateRow8_2_0_5 = ParentOwnership.parentRow0190 := by rfl
theorem patch_mem8_2_0_5 : RadiusFivePruning.patch8_2_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0190, parentRow_mem0190, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0190_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_0_5]
  rfl
theorem row_eq8_2_0_6 : RadiusFivePruning.stateRow8_2_0_6 = ParentOwnership.parentRow0191 := by rfl
theorem patch_mem8_2_0_6 : RadiusFivePruning.patch8_2_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0191, parentRow_mem0191, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0191_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_0_6]
  rfl
theorem row_eq8_2_0_7 : RadiusFivePruning.stateRow8_2_0_7 = ParentOwnership.parentRow1125 := by rfl
theorem patch_mem8_2_0_7 : RadiusFivePruning.patch8_2_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1125, parentRow_mem1125, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1125_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_0_7]
  rfl
theorem row_eq8_2_0_8 : RadiusFivePruning.stateRow8_2_0_8 = ParentOwnership.parentRow0185 := by rfl
theorem patch_mem8_2_0_8 : RadiusFivePruning.patch8_2_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0185, parentRow_mem0185, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0185_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_0_8]
  rfl
theorem row_eq8_2_0_9 : RadiusFivePruning.stateRow8_2_0_9 = ParentOwnership.parentRow0392 := by rfl
theorem patch_mem8_2_0_9 : RadiusFivePruning.patch8_2_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0392, parentRow_mem0392, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0392_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_0_9]
  rfl
theorem row_eq8_2_0_10 : RadiusFivePruning.stateRow8_2_0_10 = ParentOwnership.parentRow1126 := by rfl
theorem patch_mem8_2_0_10 : RadiusFivePruning.patch8_2_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1126, parentRow_mem1126, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1126_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_0_10]
  rfl
theorem row_eq8_2_0_11 : RadiusFivePruning.stateRow8_2_0_11 = ParentOwnership.parentRow0393 := by rfl
theorem patch_mem8_2_0_11 : RadiusFivePruning.patch8_2_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0393, parentRow_mem0393, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0393_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_0_11]
  rfl
theorem chunk_mem8_2_0 : ∀ p ∈ RadiusFivePruning.final8_2_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_2_0, List.forall_mem_cons]
  exact ⟨patch_mem8_2_0_1,⟨patch_mem8_2_0_3,⟨patch_mem8_2_0_4,⟨patch_mem8_2_0_5,⟨patch_mem8_2_0_6,⟨patch_mem8_2_0_7,⟨patch_mem8_2_0_8,⟨patch_mem8_2_0_9,⟨patch_mem8_2_0_10,⟨patch_mem8_2_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_2_1_0 : RadiusFivePruning.stateRow8_2_1_0 = ParentOwnership.parentRow0395 := by rfl
theorem patch_mem8_2_1_0 : RadiusFivePruning.patch8_2_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0395, parentRow_mem0395, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0395_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_1_0]
  rfl
theorem row_eq8_2_1_1 : RadiusFivePruning.stateRow8_2_1_1 = ParentOwnership.parentRow0391 := by rfl
theorem patch_mem8_2_1_1 : RadiusFivePruning.patch8_2_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0391, parentRow_mem0391, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0391_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_1_1]
  rfl
theorem row_eq8_2_1_2 : RadiusFivePruning.stateRow8_2_1_2 = ParentOwnership.parentRow1127 := by rfl
theorem patch_mem8_2_1_2 : RadiusFivePruning.patch8_2_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1127, parentRow_mem1127, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1127_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_1_2]
  rfl
theorem row_eq8_2_1_3 : RadiusFivePruning.stateRow8_2_1_3 = ParentOwnership.parentRow0394 := by rfl
theorem patch_mem8_2_1_3 : RadiusFivePruning.patch8_2_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0394, parentRow_mem0394, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0394_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_1_3]
  rfl
theorem row_eq8_2_1_4 : RadiusFivePruning.stateRow8_2_1_4 = ParentOwnership.parentRow0396 := by rfl
theorem patch_mem8_2_1_4 : RadiusFivePruning.patch8_2_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0396, parentRow_mem0396, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0396_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_1_4]
  rfl
theorem row_eq8_2_1_6 : RadiusFivePruning.stateRow8_2_1_6 = ParentOwnership.parentRow1123 := by rfl
theorem patch_mem8_2_1_6 : RadiusFivePruning.patch8_2_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1123, parentRow_mem1123, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1123_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_1_6]
  rfl
theorem row_eq8_2_1_8 : RadiusFivePruning.stateRow8_2_1_8 = ParentOwnership.parentRow0182 := by rfl
theorem patch_mem8_2_1_8 : RadiusFivePruning.patch8_2_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0182, parentRow_mem0182, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0182_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_1_8]
  rfl
theorem row_eq8_2_1_9 : RadiusFivePruning.stateRow8_2_1_9 = ParentOwnership.parentRow1124 := by rfl
theorem patch_mem8_2_1_9 : RadiusFivePruning.patch8_2_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1124, parentRow_mem1124, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1124_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_1_9]
  rfl
theorem row_eq8_2_1_10 : RadiusFivePruning.stateRow8_2_1_10 = ParentOwnership.parentRow0184 := by rfl
theorem patch_mem8_2_1_10 : RadiusFivePruning.patch8_2_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0184, parentRow_mem0184, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0184_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_1_10]
  rfl
theorem chunk_mem8_2_1 : ∀ p ∈ RadiusFivePruning.final8_2_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_2_1, List.forall_mem_cons]
  exact ⟨patch_mem8_2_1_0,⟨patch_mem8_2_1_1,⟨patch_mem8_2_1_2,⟨patch_mem8_2_1_3,⟨patch_mem8_2_1_4,⟨patch_mem8_2_1_6,⟨patch_mem8_2_1_8,⟨patch_mem8_2_1_9,⟨patch_mem8_2_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_2_2_0 : RadiusFivePruning.stateRow8_2_2_0 = ParentOwnership.parentRow0390 := by rfl
theorem patch_mem8_2_2_0 : RadiusFivePruning.patch8_2_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0390, parentRow_mem0390, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0390_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_2_0]
  rfl
theorem row_eq8_2_2_2 : RadiusFivePruning.stateRow8_2_2_2 = ParentOwnership.parentRow0321 := by rfl
theorem patch_mem8_2_2_2 : RadiusFivePruning.patch8_2_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0321, parentRow_mem0321, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0321_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_2_2]
  rfl
theorem row_eq8_2_2_3 : RadiusFivePruning.stateRow8_2_2_3 = ParentOwnership.parentRow0589 := by rfl
theorem patch_mem8_2_2_3 : RadiusFivePruning.patch8_2_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0589, parentRow_mem0589, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0589_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_2_3]
  rfl
theorem row_eq8_2_2_4 : RadiusFivePruning.stateRow8_2_2_4 = ParentOwnership.parentRow0324 := by rfl
theorem patch_mem8_2_2_4 : RadiusFivePruning.patch8_2_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0324, parentRow_mem0324, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0324_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_2_4]
  rfl
theorem row_eq8_2_2_5 : RadiusFivePruning.stateRow8_2_2_5 = ParentOwnership.parentRow0591 := by rfl
theorem patch_mem8_2_2_5 : RadiusFivePruning.patch8_2_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0591, parentRow_mem0591, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0591_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_2_5]
  rfl
theorem row_eq8_2_2_6 : RadiusFivePruning.stateRow8_2_2_6 = ParentOwnership.parentRow1488 := by rfl
theorem patch_mem8_2_2_6 : RadiusFivePruning.patch8_2_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1488, parentRow_mem1488, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1488_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_2_6]
  rfl
theorem row_eq8_2_2_7 : RadiusFivePruning.stateRow8_2_2_7 = ParentOwnership.parentRow1486 := by rfl
theorem patch_mem8_2_2_7 : RadiusFivePruning.patch8_2_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1486, parentRow_mem1486, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1486_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_2_7]
  rfl
theorem row_eq8_2_2_8 : RadiusFivePruning.stateRow8_2_2_8 = ParentOwnership.parentRow1487 := by rfl
theorem patch_mem8_2_2_8 : RadiusFivePruning.patch8_2_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1487, parentRow_mem1487, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1487_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_2_8]
  rfl
theorem row_eq8_2_2_9 : RadiusFivePruning.stateRow8_2_2_9 = ParentOwnership.parentRow1492 := by rfl
theorem patch_mem8_2_2_9 : RadiusFivePruning.patch8_2_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1492, parentRow_mem1492, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1492_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_2_9]
  rfl
theorem row_eq8_2_2_10 : RadiusFivePruning.stateRow8_2_2_10 = ParentOwnership.parentRow1485 := by rfl
theorem patch_mem8_2_2_10 : RadiusFivePruning.patch8_2_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1485, parentRow_mem1485, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1485_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_2_10]
  rfl
theorem row_eq8_2_2_11 : RadiusFivePruning.stateRow8_2_2_11 = ParentOwnership.parentRow1491 := by rfl
theorem patch_mem8_2_2_11 : RadiusFivePruning.patch8_2_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1491, parentRow_mem1491, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1491_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_2_11]
  rfl
theorem chunk_mem8_2_2 : ∀ p ∈ RadiusFivePruning.final8_2_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_2_2, List.forall_mem_cons]
  exact ⟨patch_mem8_2_2_0,⟨patch_mem8_2_2_2,⟨patch_mem8_2_2_3,⟨patch_mem8_2_2_4,⟨patch_mem8_2_2_5,⟨patch_mem8_2_2_6,⟨patch_mem8_2_2_7,⟨patch_mem8_2_2_8,⟨patch_mem8_2_2_9,⟨patch_mem8_2_2_10,⟨patch_mem8_2_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_2_3_0 : RadiusFivePruning.stateRow8_2_3_0 = ParentOwnership.parentRow0409 := by rfl
theorem patch_mem8_2_3_0 : RadiusFivePruning.patch8_2_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0409, parentRow_mem0409, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0409_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_3_0]
  rfl
theorem row_eq8_2_3_1 : RadiusFivePruning.stateRow8_2_3_1 = ParentOwnership.parentRow0410 := by rfl
theorem patch_mem8_2_3_1 : RadiusFivePruning.patch8_2_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0410, parentRow_mem0410, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0410_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_3_1]
  rfl
theorem row_eq8_2_3_3 : RadiusFivePruning.stateRow8_2_3_3 = ParentOwnership.parentRow0388 := by rfl
theorem patch_mem8_2_3_3 : RadiusFivePruning.patch8_2_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0388, parentRow_mem0388, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0388_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_3_3]
  rfl
theorem row_eq8_2_3_4 : RadiusFivePruning.stateRow8_2_3_4 = ParentOwnership.parentRow0389 := by rfl
theorem patch_mem8_2_3_4 : RadiusFivePruning.patch8_2_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0389, parentRow_mem0389, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0389_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_3_4]
  rfl
theorem row_eq8_2_3_5 : RadiusFivePruning.stateRow8_2_3_5 = ParentOwnership.parentRow0386 := by rfl
theorem patch_mem8_2_3_5 : RadiusFivePruning.patch8_2_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0386, parentRow_mem0386, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0386_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_3_5]
  rfl
theorem row_eq8_2_3_6 : RadiusFivePruning.stateRow8_2_3_6 = ParentOwnership.parentRow1517 := by rfl
theorem patch_mem8_2_3_6 : RadiusFivePruning.patch8_2_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1517, parentRow_mem1517, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1517_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_3_6]
  rfl
theorem row_eq8_2_3_7 : RadiusFivePruning.stateRow8_2_3_7 = ParentOwnership.parentRow1483 := by rfl
theorem patch_mem8_2_3_7 : RadiusFivePruning.patch8_2_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1483, parentRow_mem1483, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1483_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_3_7]
  rfl
theorem row_eq8_2_3_8 : RadiusFivePruning.stateRow8_2_3_8 = ParentOwnership.parentRow1489 := by rfl
theorem patch_mem8_2_3_8 : RadiusFivePruning.patch8_2_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1489, parentRow_mem1489, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1489_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_3_8]
  rfl
theorem row_eq8_2_3_9 : RadiusFivePruning.stateRow8_2_3_9 = ParentOwnership.parentRow1506 := by rfl
theorem patch_mem8_2_3_9 : RadiusFivePruning.patch8_2_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1506, parentRow_mem1506, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1506_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_3_9]
  rfl
theorem row_eq8_2_3_10 : RadiusFivePruning.stateRow8_2_3_10 = ParentOwnership.parentRow1511 := by rfl
theorem patch_mem8_2_3_10 : RadiusFivePruning.patch8_2_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1511, parentRow_mem1511, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1511_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_3_10]
  rfl
theorem row_eq8_2_3_11 : RadiusFivePruning.stateRow8_2_3_11 = ParentOwnership.parentRow1508 := by rfl
theorem patch_mem8_2_3_11 : RadiusFivePruning.patch8_2_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1508, parentRow_mem1508, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1508_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_3_11]
  rfl
theorem chunk_mem8_2_3 : ∀ p ∈ RadiusFivePruning.final8_2_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_2_3, List.forall_mem_cons]
  exact ⟨patch_mem8_2_3_0,⟨patch_mem8_2_3_1,⟨patch_mem8_2_3_3,⟨patch_mem8_2_3_4,⟨patch_mem8_2_3_5,⟨patch_mem8_2_3_6,⟨patch_mem8_2_3_7,⟨patch_mem8_2_3_8,⟨patch_mem8_2_3_9,⟨patch_mem8_2_3_10,⟨patch_mem8_2_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
