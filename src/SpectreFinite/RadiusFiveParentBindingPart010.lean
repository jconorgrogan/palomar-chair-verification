module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock1T2C0
public import SpectreFinite.RadiusFivePruningLiteralBlock1T2C1
public import SpectreFinite.RadiusFivePruningLiteralBlock1T2C2
public import SpectreFinite.RadiusFivePruningLiteralBlock1T2C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq1_2_0_1 : RadiusFivePruning.stateRow1_2_0_1 = ParentOwnership.parentRow0180 := by rfl
theorem patch_mem1_2_0_1 : RadiusFivePruning.patch1_2_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0180, parentRow_mem0180, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0180_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_0_1]
  rfl
theorem row_eq1_2_0_2 : RadiusFivePruning.stateRow1_2_0_2 = ParentOwnership.parentRow0362 := by rfl
theorem patch_mem1_2_0_2 : RadiusFivePruning.patch1_2_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0362, parentRow_mem0362, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0362_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_0_2]
  rfl
theorem row_eq1_2_0_3 : RadiusFivePruning.stateRow1_2_0_3 = ParentOwnership.parentRow0366 := by rfl
theorem patch_mem1_2_0_3 : RadiusFivePruning.patch1_2_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0366, parentRow_mem0366, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0366_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_0_3]
  rfl
theorem row_eq1_2_0_5 : RadiusFivePruning.stateRow1_2_0_5 = ParentOwnership.parentRow0357 := by rfl
theorem patch_mem1_2_0_5 : RadiusFivePruning.patch1_2_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0357, parentRow_mem0357, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0357_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_0_5]
  rfl
theorem row_eq1_2_0_6 : RadiusFivePruning.stateRow1_2_0_6 = ParentOwnership.parentRow0338 := by rfl
theorem patch_mem1_2_0_6 : RadiusFivePruning.patch1_2_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0338, parentRow_mem0338, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0338_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_0_6]
  rfl
theorem row_eq1_2_0_7 : RadiusFivePruning.stateRow1_2_0_7 = ParentOwnership.parentRow0342 := by rfl
theorem patch_mem1_2_0_7 : RadiusFivePruning.patch1_2_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0342, parentRow_mem0342, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0342_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_0_7]
  rfl
theorem row_eq1_2_0_8 : RadiusFivePruning.stateRow1_2_0_8 = ParentOwnership.parentRow0340 := by rfl
theorem patch_mem1_2_0_8 : RadiusFivePruning.patch1_2_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0340, parentRow_mem0340, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0340_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_0_8]
  rfl
theorem row_eq1_2_0_9 : RadiusFivePruning.stateRow1_2_0_9 = ParentOwnership.parentRow0344 := by rfl
theorem patch_mem1_2_0_9 : RadiusFivePruning.patch1_2_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0344, parentRow_mem0344, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0344_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_0_9]
  rfl
theorem row_eq1_2_0_10 : RadiusFivePruning.stateRow1_2_0_10 = ParentOwnership.parentRow0363 := by rfl
theorem patch_mem1_2_0_10 : RadiusFivePruning.patch1_2_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0363, parentRow_mem0363, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0363_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_0_10]
  rfl
theorem row_eq1_2_0_11 : RadiusFivePruning.stateRow1_2_0_11 = ParentOwnership.parentRow0367 := by rfl
theorem patch_mem1_2_0_11 : RadiusFivePruning.patch1_2_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0367, parentRow_mem0367, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0367_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_0_11]
  rfl
theorem chunk_mem1_2_0 : ∀ p ∈ RadiusFivePruning.final1_2_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_2_0, List.forall_mem_cons]
  exact ⟨patch_mem1_2_0_1,⟨patch_mem1_2_0_2,⟨patch_mem1_2_0_3,⟨patch_mem1_2_0_5,⟨patch_mem1_2_0_6,⟨patch_mem1_2_0_7,⟨patch_mem1_2_0_8,⟨patch_mem1_2_0_9,⟨patch_mem1_2_0_10,⟨patch_mem1_2_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_2_1_1 : RadiusFivePruning.stateRow1_2_1_1 = ParentOwnership.parentRow0339 := by rfl
theorem patch_mem1_2_1_1 : RadiusFivePruning.patch1_2_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0339, parentRow_mem0339, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0339_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_1_1]
  rfl
theorem row_eq1_2_1_2 : RadiusFivePruning.stateRow1_2_1_2 = ParentOwnership.parentRow0343 := by rfl
theorem patch_mem1_2_1_2 : RadiusFivePruning.patch1_2_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0343, parentRow_mem0343, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0343_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_1_2]
  rfl
theorem row_eq1_2_1_3 : RadiusFivePruning.stateRow1_2_1_3 = ParentOwnership.parentRow0341 := by rfl
theorem patch_mem1_2_1_3 : RadiusFivePruning.patch1_2_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0341, parentRow_mem0341, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0341_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_1_3]
  rfl
theorem row_eq1_2_1_4 : RadiusFivePruning.stateRow1_2_1_4 = ParentOwnership.parentRow0345 := by rfl
theorem patch_mem1_2_1_4 : RadiusFivePruning.patch1_2_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0345, parentRow_mem0345, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0345_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_1_4]
  rfl
theorem row_eq1_2_1_5 : RadiusFivePruning.stateRow1_2_1_5 = ParentOwnership.parentRow0358 := by rfl
theorem patch_mem1_2_1_5 : RadiusFivePruning.patch1_2_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0358, parentRow_mem0358, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0358_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_1_5]
  rfl
theorem row_eq1_2_1_6 : RadiusFivePruning.stateRow1_2_1_6 = ParentOwnership.parentRow0334 := by rfl
theorem patch_mem1_2_1_6 : RadiusFivePruning.patch1_2_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0334, parentRow_mem0334, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0334_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_1_6]
  rfl
theorem row_eq1_2_1_8 : RadiusFivePruning.stateRow1_2_1_8 = ParentOwnership.parentRow0337 := by rfl
theorem patch_mem1_2_1_8 : RadiusFivePruning.patch1_2_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0337, parentRow_mem0337, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0337_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_1_8]
  rfl
theorem row_eq1_2_1_9 : RadiusFivePruning.stateRow1_2_1_9 = ParentOwnership.parentRow1454 := by rfl
theorem patch_mem1_2_1_9 : RadiusFivePruning.patch1_2_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1454, parentRow_mem1454, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1454_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_1_9]
  rfl
theorem row_eq1_2_1_10 : RadiusFivePruning.stateRow1_2_1_10 = ParentOwnership.parentRow1450 := by rfl
theorem patch_mem1_2_1_10 : RadiusFivePruning.patch1_2_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1450, parentRow_mem1450, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1450_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_1_10]
  rfl
theorem chunk_mem1_2_1 : ∀ p ∈ RadiusFivePruning.final1_2_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_2_1, List.forall_mem_cons]
  exact ⟨patch_mem1_2_1_1,⟨patch_mem1_2_1_2,⟨patch_mem1_2_1_3,⟨patch_mem1_2_1_4,⟨patch_mem1_2_1_5,⟨patch_mem1_2_1_6,⟨patch_mem1_2_1_8,⟨patch_mem1_2_1_9,⟨patch_mem1_2_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_2_2_0 : RadiusFivePruning.stateRow1_2_2_0 = ParentOwnership.parentRow0333 := by rfl
theorem patch_mem1_2_2_0 : RadiusFivePruning.patch1_2_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0333, parentRow_mem0333, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0333_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_2_0]
  rfl
theorem row_eq1_2_2_1 : RadiusFivePruning.stateRow1_2_2_1 = ParentOwnership.parentRow1451 := by rfl
theorem patch_mem1_2_2_1 : RadiusFivePruning.patch1_2_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1451, parentRow_mem1451, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1451_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_2_1]
  rfl
theorem row_eq1_2_2_2 : RadiusFivePruning.stateRow1_2_2_2 = ParentOwnership.parentRow0336 := by rfl
theorem patch_mem1_2_2_2 : RadiusFivePruning.patch1_2_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0336, parentRow_mem0336, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0336_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_2_2]
  rfl
theorem row_eq1_2_2_3 : RadiusFivePruning.stateRow1_2_2_3 = ParentOwnership.parentRow1453 := by rfl
theorem patch_mem1_2_2_3 : RadiusFivePruning.patch1_2_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1453, parentRow_mem1453, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1453_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_2_3]
  rfl
theorem row_eq1_2_2_4 : RadiusFivePruning.stateRow1_2_2_4 = ParentOwnership.parentRow1449 := by rfl
theorem patch_mem1_2_2_4 : RadiusFivePruning.patch1_2_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1449, parentRow_mem1449, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1449_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_2_4]
  rfl
theorem row_eq1_2_2_6 : RadiusFivePruning.stateRow1_2_2_6 = ParentOwnership.parentRow1122 := by rfl
theorem patch_mem1_2_2_6 : RadiusFivePruning.patch1_2_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1122, parentRow_mem1122, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1122_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_2_6]
  rfl
theorem row_eq1_2_2_7 : RadiusFivePruning.stateRow1_2_2_7 = ParentOwnership.parentRow1119 := by rfl
theorem patch_mem1_2_2_7 : RadiusFivePruning.patch1_2_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1119, parentRow_mem1119, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1119_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_2_7]
  rfl
theorem row_eq1_2_2_8 : RadiusFivePruning.stateRow1_2_2_8 = ParentOwnership.parentRow1110 := by rfl
theorem patch_mem1_2_2_8 : RadiusFivePruning.patch1_2_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1110, parentRow_mem1110, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1110_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_2_8]
  rfl
theorem row_eq1_2_2_9 : RadiusFivePruning.stateRow1_2_2_9 = ParentOwnership.parentRow1113 := by rfl
theorem patch_mem1_2_2_9 : RadiusFivePruning.patch1_2_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1113, parentRow_mem1113, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1113_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_2_9]
  rfl
theorem row_eq1_2_2_11 : RadiusFivePruning.stateRow1_2_2_11 = ParentOwnership.parentRow0364 := by rfl
theorem patch_mem1_2_2_11 : RadiusFivePruning.patch1_2_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0364, parentRow_mem0364, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0364_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_2_11]
  rfl
theorem chunk_mem1_2_2 : ∀ p ∈ RadiusFivePruning.final1_2_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_2_2, List.forall_mem_cons]
  exact ⟨patch_mem1_2_2_0,⟨patch_mem1_2_2_1,⟨patch_mem1_2_2_2,⟨patch_mem1_2_2_3,⟨patch_mem1_2_2_4,⟨patch_mem1_2_2_6,⟨patch_mem1_2_2_7,⟨patch_mem1_2_2_8,⟨patch_mem1_2_2_9,⟨patch_mem1_2_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_2_3_0 : RadiusFivePruning.stateRow1_2_3_0 = ParentOwnership.parentRow0368 := by rfl
theorem patch_mem1_2_3_0 : RadiusFivePruning.patch1_2_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0368, parentRow_mem0368, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0368_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_3_0]
  rfl
theorem row_eq1_2_3_1 : RadiusFivePruning.stateRow1_2_3_1 = ParentOwnership.parentRow0359 := by rfl
theorem patch_mem1_2_3_1 : RadiusFivePruning.patch1_2_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0359, parentRow_mem0359, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0359_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_3_1]
  rfl
theorem row_eq1_2_3_3 : RadiusFivePruning.stateRow1_2_3_3 = ParentOwnership.parentRow1120 := by rfl
theorem patch_mem1_2_3_3 : RadiusFivePruning.patch1_2_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1120, parentRow_mem1120, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1120_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_3_3]
  rfl
theorem row_eq1_2_3_5 : RadiusFivePruning.stateRow1_2_3_5 = ParentOwnership.parentRow1111 := by rfl
theorem patch_mem1_2_3_5 : RadiusFivePruning.patch1_2_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1111, parentRow_mem1111, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1111_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_3_5]
  rfl
theorem row_eq1_2_3_6 : RadiusFivePruning.stateRow1_2_3_6 = ParentOwnership.parentRow1108 := by rfl
theorem patch_mem1_2_3_6 : RadiusFivePruning.patch1_2_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1108, parentRow_mem1108, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1108_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_3_6]
  rfl
theorem row_eq1_2_3_7 : RadiusFivePruning.stateRow1_2_3_7 = ParentOwnership.parentRow0361 := by rfl
theorem patch_mem1_2_3_7 : RadiusFivePruning.patch1_2_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0361, parentRow_mem0361, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0361_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_3_7]
  rfl
theorem row_eq1_2_3_8 : RadiusFivePruning.stateRow1_2_3_8 = ParentOwnership.parentRow0365 := by rfl
theorem patch_mem1_2_3_8 : RadiusFivePruning.patch1_2_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0365, parentRow_mem0365, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0365_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_3_8]
  rfl
theorem row_eq1_2_3_9 : RadiusFivePruning.stateRow1_2_3_9 = ParentOwnership.parentRow0360 := by rfl
theorem patch_mem1_2_3_9 : RadiusFivePruning.patch1_2_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0360, parentRow_mem0360, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0360_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_3_9]
  rfl
theorem row_eq1_2_3_10 : RadiusFivePruning.stateRow1_2_3_10 = ParentOwnership.parentRow0220 := by rfl
theorem patch_mem1_2_3_10 : RadiusFivePruning.patch1_2_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0220, parentRow_mem0220, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0220_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_3_10]
  rfl
theorem row_eq1_2_3_11 : RadiusFivePruning.stateRow1_2_3_11 = ParentOwnership.parentRow1121 := by rfl
theorem patch_mem1_2_3_11 : RadiusFivePruning.patch1_2_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1121, parentRow_mem1121, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1121_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_3_11]
  rfl
theorem chunk_mem1_2_3 : ∀ p ∈ RadiusFivePruning.final1_2_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_2_3, List.forall_mem_cons]
  exact ⟨patch_mem1_2_3_0,⟨patch_mem1_2_3_1,⟨patch_mem1_2_3_3,⟨patch_mem1_2_3_5,⟨patch_mem1_2_3_6,⟨patch_mem1_2_3_7,⟨patch_mem1_2_3_8,⟨patch_mem1_2_3_9,⟨patch_mem1_2_3_10,⟨patch_mem1_2_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
