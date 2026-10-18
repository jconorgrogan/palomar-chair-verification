module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock8T2C4
public import SpectreFinite.RadiusFivePruningLiteralBlock8T2C5
public import SpectreFinite.RadiusFivePruningLiteralBlock8T3C0
public import SpectreFinite.RadiusFivePruningLiteralBlock8T3C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq8_2_4_0 : RadiusFivePruning.stateRow8_2_4_0 = ParentOwnership.parentRow1513 := by rfl
theorem patch_mem8_2_4_0 : RadiusFivePruning.patch8_2_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1513, parentRow_mem1513, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1513_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_4_0]
  rfl
theorem row_eq8_2_4_1 : RadiusFivePruning.stateRow8_2_4_1 = ParentOwnership.parentRow0407 := by rfl
theorem patch_mem8_2_4_1 : RadiusFivePruning.patch8_2_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0407, parentRow_mem0407, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0407_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_4_1]
  rfl
theorem row_eq8_2_4_2 : RadiusFivePruning.stateRow8_2_4_2 = ParentOwnership.parentRow0405 := by rfl
theorem patch_mem8_2_4_2 : RadiusFivePruning.patch8_2_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0405, parentRow_mem0405, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0405_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_4_2]
  rfl
theorem row_eq8_2_4_3 : RadiusFivePruning.stateRow8_2_4_3 = ParentOwnership.parentRow0408 := by rfl
theorem patch_mem8_2_4_3 : RadiusFivePruning.patch8_2_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0408, parentRow_mem0408, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0408_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_4_3]
  rfl
theorem row_eq8_2_4_4 : RadiusFivePruning.stateRow8_2_4_4 = ParentOwnership.parentRow0406 := by rfl
theorem patch_mem8_2_4_4 : RadiusFivePruning.patch8_2_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0406, parentRow_mem0406, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0406_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_4_4]
  rfl
theorem row_eq8_2_4_5 : RadiusFivePruning.stateRow8_2_4_5 = ParentOwnership.parentRow0398 := by rfl
theorem patch_mem8_2_4_5 : RadiusFivePruning.patch8_2_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0398, parentRow_mem0398, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0398_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_4_5]
  rfl
theorem row_eq8_2_4_8 : RadiusFivePruning.stateRow8_2_4_8 = ParentOwnership.parentRow0375 := by rfl
theorem patch_mem8_2_4_8 : RadiusFivePruning.patch8_2_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0375, parentRow_mem0375, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0375_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_4_8]
  rfl
theorem row_eq8_2_4_9 : RadiusFivePruning.stateRow8_2_4_9 = ParentOwnership.parentRow0383 := by rfl
theorem patch_mem8_2_4_9 : RadiusFivePruning.patch8_2_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0383, parentRow_mem0383, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0383_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_4_9]
  rfl
theorem row_eq8_2_4_10 : RadiusFivePruning.stateRow8_2_4_10 = ParentOwnership.parentRow0384 := by rfl
theorem patch_mem8_2_4_10 : RadiusFivePruning.patch8_2_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0384, parentRow_mem0384, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0384_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_4_10]
  rfl
theorem row_eq8_2_4_11 : RadiusFivePruning.stateRow8_2_4_11 = ParentOwnership.parentRow1510 := by rfl
theorem patch_mem8_2_4_11 : RadiusFivePruning.patch8_2_4_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1510, parentRow_mem1510, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1510_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_4_11]
  rfl
theorem chunk_mem8_2_4 : ∀ p ∈ RadiusFivePruning.final8_2_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_2_4, List.forall_mem_cons]
  exact ⟨patch_mem8_2_4_0,⟨patch_mem8_2_4_1,⟨patch_mem8_2_4_2,⟨patch_mem8_2_4_3,⟨patch_mem8_2_4_4,⟨patch_mem8_2_4_5,⟨patch_mem8_2_4_8,⟨patch_mem8_2_4_9,⟨patch_mem8_2_4_10,⟨patch_mem8_2_4_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_2_5_0 : RadiusFivePruning.stateRow8_2_5_0 = ParentOwnership.parentRow1515 := by rfl
theorem patch_mem8_2_5_0 : RadiusFivePruning.patch8_2_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1515, parentRow_mem1515, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1515_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_5_0]
  rfl
theorem row_eq8_2_5_1 : RadiusFivePruning.stateRow8_2_5_1 = ParentOwnership.parentRow0387 := by rfl
theorem patch_mem8_2_5_1 : RadiusFivePruning.patch8_2_5_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0387, parentRow_mem0387, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0387_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_5_1]
  rfl
theorem row_eq8_2_5_2 : RadiusFivePruning.stateRow8_2_5_2 = ParentOwnership.parentRow0385 := by rfl
theorem patch_mem8_2_5_2 : RadiusFivePruning.patch8_2_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0385, parentRow_mem0385, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0385_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_5_2]
  rfl
theorem row_eq8_2_5_3 : RadiusFivePruning.stateRow8_2_5_3 = ParentOwnership.parentRow1516 := by rfl
theorem patch_mem8_2_5_3 : RadiusFivePruning.patch8_2_5_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1516, parentRow_mem1516, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1516_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_5_3]
  rfl
theorem row_eq8_2_5_4 : RadiusFivePruning.stateRow8_2_5_4 = ParentOwnership.parentRow1484 := by rfl
theorem patch_mem8_2_5_4 : RadiusFivePruning.patch8_2_5_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1484, parentRow_mem1484, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1484_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_5_4]
  rfl
theorem row_eq8_2_5_5 : RadiusFivePruning.stateRow8_2_5_5 = ParentOwnership.parentRow1490 := by rfl
theorem patch_mem8_2_5_5 : RadiusFivePruning.patch8_2_5_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1490, parentRow_mem1490, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1490_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_5_5]
  rfl
theorem row_eq8_2_5_6 : RadiusFivePruning.stateRow8_2_5_6 = ParentOwnership.parentRow1507 := by rfl
theorem patch_mem8_2_5_6 : RadiusFivePruning.patch8_2_5_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1507, parentRow_mem1507, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1507_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_5_6]
  rfl
theorem row_eq8_2_5_7 : RadiusFivePruning.stateRow8_2_5_7 = ParentOwnership.parentRow1512 := by rfl
theorem patch_mem8_2_5_7 : RadiusFivePruning.patch8_2_5_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1512, parentRow_mem1512, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1512_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_5_7]
  rfl
theorem row_eq8_2_5_8 : RadiusFivePruning.stateRow8_2_5_8 = ParentOwnership.parentRow1509 := by rfl
theorem patch_mem8_2_5_8 : RadiusFivePruning.patch8_2_5_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1509, parentRow_mem1509, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1509_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_5_8]
  rfl
theorem row_eq8_2_5_9 : RadiusFivePruning.stateRow8_2_5_9 = ParentOwnership.parentRow1514 := by rfl
theorem patch_mem8_2_5_9 : RadiusFivePruning.patch8_2_5_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1514, parentRow_mem1514, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1514_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_2_5_9]
  rfl
theorem chunk_mem8_2_5 : ∀ p ∈ RadiusFivePruning.final8_2_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_2_5, List.forall_mem_cons]
  exact ⟨patch_mem8_2_5_0,⟨patch_mem8_2_5_1,⟨patch_mem8_2_5_2,⟨patch_mem8_2_5_3,⟨patch_mem8_2_5_4,⟨patch_mem8_2_5_5,⟨patch_mem8_2_5_6,⟨patch_mem8_2_5_7,⟨patch_mem8_2_5_8,⟨patch_mem8_2_5_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_3_0_1 : RadiusFivePruning.stateRow8_3_0_1 = ParentOwnership.parentRow1213 := by rfl
theorem patch_mem8_3_0_1 : RadiusFivePruning.patch8_3_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1213, parentRow_mem1213, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1213_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_0_1]
  rfl
theorem row_eq8_3_0_3 : RadiusFivePruning.stateRow8_3_0_3 = ParentOwnership.parentRow1212 := by rfl
theorem patch_mem8_3_0_3 : RadiusFivePruning.patch8_3_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1212, parentRow_mem1212, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1212_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_0_3]
  rfl
theorem row_eq8_3_0_4 : RadiusFivePruning.stateRow8_3_0_4 = ParentOwnership.parentRow1214 := by rfl
theorem patch_mem8_3_0_4 : RadiusFivePruning.patch8_3_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1214, parentRow_mem1214, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1214_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_0_4]
  rfl
theorem row_eq8_3_0_5 : RadiusFivePruning.stateRow8_3_0_5 = ParentOwnership.parentRow1235 := by rfl
theorem patch_mem8_3_0_5 : RadiusFivePruning.patch8_3_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1235, parentRow_mem1235, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1235_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_0_5]
  rfl
theorem row_eq8_3_0_6 : RadiusFivePruning.stateRow8_3_0_6 = ParentOwnership.parentRow1237 := by rfl
theorem patch_mem8_3_0_6 : RadiusFivePruning.patch8_3_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1237, parentRow_mem1237, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1237_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_0_6]
  rfl
theorem row_eq8_3_0_7 : RadiusFivePruning.stateRow8_3_0_7 = ParentOwnership.parentRow1216 := by rfl
theorem patch_mem8_3_0_7 : RadiusFivePruning.patch8_3_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1216, parentRow_mem1216, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1216_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_0_7]
  rfl
theorem row_eq8_3_0_8 : RadiusFivePruning.stateRow8_3_0_8 = ParentOwnership.parentRow0025 := by rfl
theorem patch_mem8_3_0_8 : RadiusFivePruning.patch8_3_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0025, parentRow_mem0025, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0025_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_0_8]
  rfl
theorem row_eq8_3_0_9 : RadiusFivePruning.stateRow8_3_0_9 = ParentOwnership.parentRow0473 := by rfl
theorem patch_mem8_3_0_9 : RadiusFivePruning.patch8_3_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0473, parentRow_mem0473, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0473_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_0_9]
  rfl
theorem row_eq8_3_0_10 : RadiusFivePruning.stateRow8_3_0_10 = ParentOwnership.parentRow1236 := by rfl
theorem patch_mem8_3_0_10 : RadiusFivePruning.patch8_3_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1236, parentRow_mem1236, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1236_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_0_10]
  rfl
theorem row_eq8_3_0_11 : RadiusFivePruning.stateRow8_3_0_11 = ParentOwnership.parentRow0477 := by rfl
theorem patch_mem8_3_0_11 : RadiusFivePruning.patch8_3_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0477, parentRow_mem0477, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0477_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_0_11]
  rfl
theorem chunk_mem8_3_0 : ∀ p ∈ RadiusFivePruning.final8_3_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_3_0, List.forall_mem_cons]
  exact ⟨patch_mem8_3_0_1,⟨patch_mem8_3_0_3,⟨patch_mem8_3_0_4,⟨patch_mem8_3_0_5,⟨patch_mem8_3_0_6,⟨patch_mem8_3_0_7,⟨patch_mem8_3_0_8,⟨patch_mem8_3_0_9,⟨patch_mem8_3_0_10,⟨patch_mem8_3_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_3_1_0 : RadiusFivePruning.stateRow8_3_1_0 = ParentOwnership.parentRow0483 := by rfl
theorem patch_mem8_3_1_0 : RadiusFivePruning.patch8_3_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0483, parentRow_mem0483, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0483_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_1_0]
  rfl
theorem row_eq8_3_1_1 : RadiusFivePruning.stateRow8_3_1_1 = ParentOwnership.parentRow0468 := by rfl
theorem patch_mem8_3_1_1 : RadiusFivePruning.patch8_3_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0468, parentRow_mem0468, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0468_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_1_1]
  rfl
theorem row_eq8_3_1_2 : RadiusFivePruning.stateRow8_3_1_2 = ParentOwnership.parentRow1238 := by rfl
theorem patch_mem8_3_1_2 : RadiusFivePruning.patch8_3_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1238, parentRow_mem1238, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1238_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_1_2]
  rfl
theorem row_eq8_3_1_3 : RadiusFivePruning.stateRow8_3_1_3 = ParentOwnership.parentRow0478 := by rfl
theorem patch_mem8_3_1_3 : RadiusFivePruning.patch8_3_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0478, parentRow_mem0478, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0478_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_1_3]
  rfl
theorem row_eq8_3_1_4 : RadiusFivePruning.stateRow8_3_1_4 = ParentOwnership.parentRow0484 := by rfl
theorem patch_mem8_3_1_4 : RadiusFivePruning.patch8_3_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0484, parentRow_mem0484, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0484_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_1_4]
  rfl
theorem row_eq8_3_1_6 : RadiusFivePruning.stateRow8_3_1_6 = ParentOwnership.parentRow1209 := by rfl
theorem patch_mem8_3_1_6 : RadiusFivePruning.patch8_3_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1209, parentRow_mem1209, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1209_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_1_6]
  rfl
theorem row_eq8_3_1_8 : RadiusFivePruning.stateRow8_3_1_8 = ParentOwnership.parentRow0014 := by rfl
theorem patch_mem8_3_1_8 : RadiusFivePruning.patch8_3_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0014, parentRow_mem0014, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0014_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_1_8]
  rfl
theorem row_eq8_3_1_9 : RadiusFivePruning.stateRow8_3_1_9 = ParentOwnership.parentRow1215 := by rfl
theorem patch_mem8_3_1_9 : RadiusFivePruning.patch8_3_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1215, parentRow_mem1215, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1215_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_1_9]
  rfl
theorem row_eq8_3_1_10 : RadiusFivePruning.stateRow8_3_1_10 = ParentOwnership.parentRow0024 := by rfl
theorem patch_mem8_3_1_10 : RadiusFivePruning.patch8_3_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0024, parentRow_mem0024, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0024_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_3_1_10]
  rfl
theorem chunk_mem8_3_1 : ∀ p ∈ RadiusFivePruning.final8_3_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_3_1, List.forall_mem_cons]
  exact ⟨patch_mem8_3_1_0,⟨patch_mem8_3_1_1,⟨patch_mem8_3_1_2,⟨patch_mem8_3_1_3,⟨patch_mem8_3_1_4,⟨patch_mem8_3_1_6,⟨patch_mem8_3_1_8,⟨patch_mem8_3_1_9,⟨patch_mem8_3_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
