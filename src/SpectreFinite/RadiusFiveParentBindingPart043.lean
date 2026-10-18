module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock7T2C4
public import SpectreFinite.RadiusFivePruningLiteralBlock7T2C5
public import SpectreFinite.RadiusFivePruningLiteralBlock7T2C6
public import SpectreFinite.RadiusFivePruningLiteralBlock7T2C7

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq7_2_4_1 : RadiusFivePruning.stateRow7_2_4_1 = ParentOwnership.parentRow1408 := by rfl
theorem patch_mem7_2_4_1 : RadiusFivePruning.patch7_2_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1408, parentRow_mem1408, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1408_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_4_1]
  rfl
theorem row_eq7_2_4_2 : RadiusFivePruning.stateRow7_2_4_2 = ParentOwnership.parentRow1448 := by rfl
theorem patch_mem7_2_4_2 : RadiusFivePruning.patch7_2_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1448, parentRow_mem1448, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1448_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_4_2]
  rfl
theorem row_eq7_2_4_3 : RadiusFivePruning.stateRow7_2_4_3 = ParentOwnership.parentRow0328 := by rfl
theorem patch_mem7_2_4_3 : RadiusFivePruning.patch7_2_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0328, parentRow_mem0328, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0328_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_4_3]
  rfl
theorem row_eq7_2_4_4 : RadiusFivePruning.stateRow7_2_4_4 = ParentOwnership.parentRow1430 := by rfl
theorem patch_mem7_2_4_4 : RadiusFivePruning.patch7_2_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1430, parentRow_mem1430, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1430_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_4_4]
  rfl
theorem row_eq7_2_4_5 : RadiusFivePruning.stateRow7_2_4_5 = ParentOwnership.parentRow1447 := by rfl
theorem patch_mem7_2_4_5 : RadiusFivePruning.patch7_2_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1447, parentRow_mem1447, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1447_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_4_5]
  rfl
theorem row_eq7_2_4_8 : RadiusFivePruning.stateRow7_2_4_8 = ParentOwnership.parentRow0352 := by rfl
theorem patch_mem7_2_4_8 : RadiusFivePruning.patch7_2_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0352, parentRow_mem0352, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0352_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_4_8]
  rfl
theorem row_eq7_2_4_10 : RadiusFivePruning.stateRow7_2_4_10 = ParentOwnership.parentRow1436 := by rfl
theorem patch_mem7_2_4_10 : RadiusFivePruning.patch7_2_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1436, parentRow_mem1436, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1436_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_4_10]
  rfl
theorem chunk_mem7_2_4 : ∀ p ∈ RadiusFivePruning.final7_2_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_2_4, List.forall_mem_cons]
  exact ⟨patch_mem7_2_4_1,⟨patch_mem7_2_4_2,⟨patch_mem7_2_4_3,⟨patch_mem7_2_4_4,⟨patch_mem7_2_4_5,⟨patch_mem7_2_4_8,⟨patch_mem7_2_4_10,by simp⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_2_5_0 : RadiusFivePruning.stateRow7_2_5_0 = ParentOwnership.parentRow0326 := by rfl
theorem patch_mem7_2_5_0 : RadiusFivePruning.patch7_2_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0326, parentRow_mem0326, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0326_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_5_0]
  rfl
theorem row_eq7_2_5_2 : RadiusFivePruning.stateRow7_2_5_2 = ParentOwnership.parentRow1435 := by rfl
theorem patch_mem7_2_5_2 : RadiusFivePruning.patch7_2_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1435, parentRow_mem1435, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1435_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_5_2]
  rfl
theorem row_eq7_2_5_3 : RadiusFivePruning.stateRow7_2_5_3 = ParentOwnership.parentRow1442 := by rfl
theorem patch_mem7_2_5_3 : RadiusFivePruning.patch7_2_5_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1442, parentRow_mem1442, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1442_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_5_3]
  rfl
theorem row_eq7_2_5_4 : RadiusFivePruning.stateRow7_2_5_4 = ParentOwnership.parentRow0211 := by rfl
theorem patch_mem7_2_5_4 : RadiusFivePruning.patch7_2_5_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0211, parentRow_mem0211, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0211_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_5_4]
  rfl
theorem row_eq7_2_5_5 : RadiusFivePruning.stateRow7_2_5_5 = ParentOwnership.parentRow0207 := by rfl
theorem patch_mem7_2_5_5 : RadiusFivePruning.patch7_2_5_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0207, parentRow_mem0207, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0207_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_5_5]
  rfl
theorem row_eq7_2_5_6 : RadiusFivePruning.stateRow7_2_5_6 = ParentOwnership.parentRow0193 := by rfl
theorem patch_mem7_2_5_6 : RadiusFivePruning.patch7_2_5_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0193, parentRow_mem0193, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0193_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_5_6]
  rfl
theorem row_eq7_2_5_7 : RadiusFivePruning.stateRow7_2_5_7 = ParentOwnership.parentRow0206 := by rfl
theorem patch_mem7_2_5_7 : RadiusFivePruning.patch7_2_5_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0206, parentRow_mem0206, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0206_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_5_7]
  rfl
theorem row_eq7_2_5_8 : RadiusFivePruning.stateRow7_2_5_8 = ParentOwnership.parentRow0351 := by rfl
theorem patch_mem7_2_5_8 : RadiusFivePruning.patch7_2_5_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0351, parentRow_mem0351, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0351_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_5_8]
  rfl
theorem row_eq7_2_5_9 : RadiusFivePruning.stateRow7_2_5_9 = ParentOwnership.parentRow0356 := by rfl
theorem patch_mem7_2_5_9 : RadiusFivePruning.patch7_2_5_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0356, parentRow_mem0356, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0356_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_5_9]
  rfl
theorem row_eq7_2_5_10 : RadiusFivePruning.stateRow7_2_5_10 = ParentOwnership.parentRow0350 := by rfl
theorem patch_mem7_2_5_10 : RadiusFivePruning.patch7_2_5_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0350, parentRow_mem0350, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0350_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_5_10]
  rfl
theorem row_eq7_2_5_11 : RadiusFivePruning.stateRow7_2_5_11 = ParentOwnership.parentRow0214 := by rfl
theorem patch_mem7_2_5_11 : RadiusFivePruning.patch7_2_5_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0214, parentRow_mem0214, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0214_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_5_11]
  rfl
theorem chunk_mem7_2_5 : ∀ p ∈ RadiusFivePruning.final7_2_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_2_5, List.forall_mem_cons]
  exact ⟨patch_mem7_2_5_0,⟨patch_mem7_2_5_2,⟨patch_mem7_2_5_3,⟨patch_mem7_2_5_4,⟨patch_mem7_2_5_5,⟨patch_mem7_2_5_6,⟨patch_mem7_2_5_7,⟨patch_mem7_2_5_8,⟨patch_mem7_2_5_9,⟨patch_mem7_2_5_10,⟨patch_mem7_2_5_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_2_6_0 : RadiusFivePruning.stateRow7_2_6_0 = ParentOwnership.parentRow0209 := by rfl
theorem patch_mem7_2_6_0 : RadiusFivePruning.patch7_2_6_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0209, parentRow_mem0209, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0209_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_6_0]
  rfl
theorem row_eq7_2_6_1 : RadiusFivePruning.stateRow7_2_6_1 = ParentOwnership.parentRow0196 := by rfl
theorem patch_mem7_2_6_1 : RadiusFivePruning.patch7_2_6_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0196, parentRow_mem0196, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0196_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_6_1]
  rfl
theorem row_eq7_2_6_2 : RadiusFivePruning.stateRow7_2_6_2 = ParentOwnership.parentRow0208 := by rfl
theorem patch_mem7_2_6_2 : RadiusFivePruning.patch7_2_6_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0208, parentRow_mem0208, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0208_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_6_2]
  rfl
theorem row_eq7_2_6_4 : RadiusFivePruning.stateRow7_2_6_4 = ParentOwnership.parentRow0192 := by rfl
theorem patch_mem7_2_6_4 : RadiusFivePruning.patch7_2_6_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0192, parentRow_mem0192, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0192_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_6_4]
  rfl
theorem row_eq7_2_6_6 : RadiusFivePruning.stateRow7_2_6_6 = ParentOwnership.parentRow0203 := by rfl
theorem patch_mem7_2_6_6 : RadiusFivePruning.patch7_2_6_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0203, parentRow_mem0203, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0203_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_6_6]
  rfl
theorem row_eq7_2_6_7 : RadiusFivePruning.stateRow7_2_6_7 = ParentOwnership.parentRow0205 := by rfl
theorem patch_mem7_2_6_7 : RadiusFivePruning.patch7_2_6_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0205, parentRow_mem0205, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0205_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_6_7]
  rfl
theorem row_eq7_2_6_9 : RadiusFivePruning.stateRow7_2_6_9 = ParentOwnership.parentRow0348 := by rfl
theorem patch_mem7_2_6_9 : RadiusFivePruning.patch7_2_6_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0348, parentRow_mem0348, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0348_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_6_9]
  rfl
theorem row_eq7_2_6_10 : RadiusFivePruning.stateRow7_2_6_10 = ParentOwnership.parentRow0349 := by rfl
theorem patch_mem7_2_6_10 : RadiusFivePruning.patch7_2_6_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0349, parentRow_mem0349, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0349_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_6_10]
  rfl
theorem row_eq7_2_6_11 : RadiusFivePruning.stateRow7_2_6_11 = ParentOwnership.parentRow0354 := by rfl
theorem patch_mem7_2_6_11 : RadiusFivePruning.patch7_2_6_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0354, parentRow_mem0354, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0354_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_6_11]
  rfl
theorem chunk_mem7_2_6 : ∀ p ∈ RadiusFivePruning.final7_2_6, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_2_6, List.forall_mem_cons]
  exact ⟨patch_mem7_2_6_0,⟨patch_mem7_2_6_1,⟨patch_mem7_2_6_2,⟨patch_mem7_2_6_4,⟨patch_mem7_2_6_6,⟨patch_mem7_2_6_7,⟨patch_mem7_2_6_9,⟨patch_mem7_2_6_10,⟨patch_mem7_2_6_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_2_7_0 : RadiusFivePruning.stateRow7_2_7_0 = ParentOwnership.parentRow0355 := by rfl
theorem patch_mem7_2_7_0 : RadiusFivePruning.patch7_2_7_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0355, parentRow_mem0355, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0355_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_7_0]
  rfl
theorem row_eq7_2_7_1 : RadiusFivePruning.stateRow7_2_7_1 = ParentOwnership.parentRow0212 := by rfl
theorem patch_mem7_2_7_1 : RadiusFivePruning.patch7_2_7_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0212, parentRow_mem0212, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0212_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_7_1]
  rfl
theorem row_eq7_2_7_2 : RadiusFivePruning.stateRow7_2_7_2 = ParentOwnership.parentRow0213 := by rfl
theorem patch_mem7_2_7_2 : RadiusFivePruning.patch7_2_7_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0213, parentRow_mem0213, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0213_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_7_2]
  rfl
theorem row_eq7_2_7_3 : RadiusFivePruning.stateRow7_2_7_3 = ParentOwnership.parentRow0194 := by rfl
theorem patch_mem7_2_7_3 : RadiusFivePruning.patch7_2_7_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0194, parentRow_mem0194, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0194_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_7_3]
  rfl
theorem row_eq7_2_7_4 : RadiusFivePruning.stateRow7_2_7_4 = ParentOwnership.parentRow0195 := by rfl
theorem patch_mem7_2_7_4 : RadiusFivePruning.patch7_2_7_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0195, parentRow_mem0195, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0195_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_7_4]
  rfl
theorem row_eq7_2_7_5 : RadiusFivePruning.stateRow7_2_7_5 = ParentOwnership.parentRow0215 := by rfl
theorem patch_mem7_2_7_5 : RadiusFivePruning.patch7_2_7_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0215, parentRow_mem0215, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0215_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_7_5]
  rfl
theorem row_eq7_2_7_6 : RadiusFivePruning.stateRow7_2_7_6 = ParentOwnership.parentRow0210 := by rfl
theorem patch_mem7_2_7_6 : RadiusFivePruning.patch7_2_7_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0210, parentRow_mem0210, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0210_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_7_6]
  rfl
theorem row_eq7_2_7_11 : RadiusFivePruning.stateRow7_2_7_11 = ParentOwnership.parentRow0204 := by rfl
theorem patch_mem7_2_7_11 : RadiusFivePruning.patch7_2_7_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0204, parentRow_mem0204, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0204_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_7_11]
  rfl
theorem chunk_mem7_2_7 : ∀ p ∈ RadiusFivePruning.final7_2_7, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_2_7, List.forall_mem_cons]
  exact ⟨patch_mem7_2_7_0,⟨patch_mem7_2_7_1,⟨patch_mem7_2_7_2,⟨patch_mem7_2_7_3,⟨patch_mem7_2_7_4,⟨patch_mem7_2_7_5,⟨patch_mem7_2_7_6,⟨patch_mem7_2_7_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
