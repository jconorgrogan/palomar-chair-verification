module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock6T3C4
public import SpectreFinite.RadiusFivePruningLiteralBlock6T3C5
public import SpectreFinite.RadiusFivePruningLiteralBlock6T4C0
public import SpectreFinite.RadiusFivePruningLiteralBlock6T4C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq6_3_4_0 : RadiusFivePruning.stateRow6_3_4_0 = ParentOwnership.parentRow0083 := by rfl
theorem patch_mem6_3_4_0 : RadiusFivePruning.patch6_3_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0083, parentRow_mem0083, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0083_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_4_0]
  rfl
theorem row_eq6_3_4_1 : RadiusFivePruning.stateRow6_3_4_1 = ParentOwnership.parentRow1081 := by rfl
theorem patch_mem6_3_4_1 : RadiusFivePruning.patch6_3_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1081, parentRow_mem1081, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1081_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_4_1]
  rfl
theorem row_eq6_3_4_2 : RadiusFivePruning.stateRow6_3_4_2 = ParentOwnership.parentRow1080 := by rfl
theorem patch_mem6_3_4_2 : RadiusFivePruning.patch6_3_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1080, parentRow_mem1080, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1080_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_4_2]
  rfl
theorem row_eq6_3_4_3 : RadiusFivePruning.stateRow6_3_4_3 = ParentOwnership.parentRow0084 := by rfl
theorem patch_mem6_3_4_3 : RadiusFivePruning.patch6_3_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0084, parentRow_mem0084, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0084_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_4_3]
  rfl
theorem row_eq6_3_4_4 : RadiusFivePruning.stateRow6_3_4_4 = ParentOwnership.parentRow1070 := by rfl
theorem patch_mem6_3_4_4 : RadiusFivePruning.patch6_3_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1070, parentRow_mem1070, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1070_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_4_4]
  rfl
theorem row_eq6_3_4_5 : RadiusFivePruning.stateRow6_3_4_5 = ParentOwnership.parentRow0086 := by rfl
theorem patch_mem6_3_4_5 : RadiusFivePruning.patch6_3_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0086, parentRow_mem0086, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0086_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_4_5]
  rfl
theorem row_eq6_3_4_6 : RadiusFivePruning.stateRow6_3_4_6 = ParentOwnership.parentRow1072 := by rfl
theorem patch_mem6_3_4_6 : RadiusFivePruning.patch6_3_4_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1072, parentRow_mem1072, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1072_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_4_6]
  rfl
theorem row_eq6_3_4_7 : RadiusFivePruning.stateRow6_3_4_7 = ParentOwnership.parentRow1063 := by rfl
theorem patch_mem6_3_4_7 : RadiusFivePruning.patch6_3_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1063, parentRow_mem1063, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1063_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_4_7]
  rfl
theorem row_eq6_3_4_8 : RadiusFivePruning.stateRow6_3_4_8 = ParentOwnership.parentRow0085 := by rfl
theorem patch_mem6_3_4_8 : RadiusFivePruning.patch6_3_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0085, parentRow_mem0085, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0085_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_4_8]
  rfl
theorem row_eq6_3_4_9 : RadiusFivePruning.stateRow6_3_4_9 = ParentOwnership.parentRow1071 := by rfl
theorem patch_mem6_3_4_9 : RadiusFivePruning.patch6_3_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1071, parentRow_mem1071, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1071_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_4_9]
  rfl
theorem row_eq6_3_4_10 : RadiusFivePruning.stateRow6_3_4_10 = ParentOwnership.parentRow0087 := by rfl
theorem patch_mem6_3_4_10 : RadiusFivePruning.patch6_3_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0087, parentRow_mem0087, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0087_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_4_10]
  rfl
theorem row_eq6_3_4_11 : RadiusFivePruning.stateRow6_3_4_11 = ParentOwnership.parentRow1073 := by rfl
theorem patch_mem6_3_4_11 : RadiusFivePruning.patch6_3_4_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1073, parentRow_mem1073, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1073_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_4_11]
  rfl
theorem chunk_mem6_3_4 : ∀ p ∈ RadiusFivePruning.final6_3_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_3_4, List.forall_mem_cons]
  exact ⟨patch_mem6_3_4_0,⟨patch_mem6_3_4_1,⟨patch_mem6_3_4_2,⟨patch_mem6_3_4_3,⟨patch_mem6_3_4_4,⟨patch_mem6_3_4_5,⟨patch_mem6_3_4_6,⟨patch_mem6_3_4_7,⟨patch_mem6_3_4_8,⟨patch_mem6_3_4_9,⟨patch_mem6_3_4_10,⟨patch_mem6_3_4_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_3_5_0 : RadiusFivePruning.stateRow6_3_5_0 = ParentOwnership.parentRow1065 := by rfl
theorem patch_mem6_3_5_0 : RadiusFivePruning.patch6_3_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1065, parentRow_mem1065, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1065_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_5_0]
  rfl
theorem row_eq6_3_5_1 : RadiusFivePruning.stateRow6_3_5_1 = ParentOwnership.parentRow1049 := by rfl
theorem patch_mem6_3_5_1 : RadiusFivePruning.patch6_3_5_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1049, parentRow_mem1049, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1049_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_5_1]
  rfl
theorem row_eq6_3_5_2 : RadiusFivePruning.stateRow6_3_5_2 = ParentOwnership.parentRow1057 := by rfl
theorem patch_mem6_3_5_2 : RadiusFivePruning.patch6_3_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1057, parentRow_mem1057, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1057_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_5_2]
  rfl
theorem chunk_mem6_3_5 : ∀ p ∈ RadiusFivePruning.final6_3_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_3_5, List.forall_mem_cons]
  exact ⟨patch_mem6_3_5_0,⟨patch_mem6_3_5_1,⟨patch_mem6_3_5_2,by simp⟩⟩⟩
theorem row_eq6_4_0_2 : RadiusFivePruning.stateRow6_4_0_2 = ParentOwnership.parentRow1293 := by rfl
theorem patch_mem6_4_0_2 : RadiusFivePruning.patch6_4_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1293, parentRow_mem1293, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1293_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_0_2]
  rfl
theorem row_eq6_4_0_3 : RadiusFivePruning.stateRow6_4_0_3 = ParentOwnership.parentRow1292 := by rfl
theorem patch_mem6_4_0_3 : RadiusFivePruning.patch6_4_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1292, parentRow_mem1292, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1292_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_0_3]
  rfl
theorem row_eq6_4_0_5 : RadiusFivePruning.stateRow6_4_0_5 = ParentOwnership.parentRow1294 := by rfl
theorem patch_mem6_4_0_5 : RadiusFivePruning.patch6_4_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1294, parentRow_mem1294, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1294_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_0_5]
  rfl
theorem row_eq6_4_0_6 : RadiusFivePruning.stateRow6_4_0_6 = ParentOwnership.parentRow1286 := by rfl
theorem patch_mem6_4_0_6 : RadiusFivePruning.patch6_4_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1286, parentRow_mem1286, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1286_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_0_6]
  rfl
theorem row_eq6_4_0_8 : RadiusFivePruning.stateRow6_4_0_8 = ParentOwnership.parentRow0113 := by rfl
theorem patch_mem6_4_0_8 : RadiusFivePruning.patch6_4_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0113, parentRow_mem0113, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0113_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_0_8]
  rfl
theorem row_eq6_4_0_10 : RadiusFivePruning.stateRow6_4_0_10 = ParentOwnership.parentRow0117 := by rfl
theorem patch_mem6_4_0_10 : RadiusFivePruning.patch6_4_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0117, parentRow_mem0117, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0117_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_0_10]
  rfl
theorem chunk_mem6_4_0 : ∀ p ∈ RadiusFivePruning.final6_4_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_4_0, List.forall_mem_cons]
  exact ⟨patch_mem6_4_0_2,⟨patch_mem6_4_0_3,⟨patch_mem6_4_0_5,⟨patch_mem6_4_0_6,⟨patch_mem6_4_0_8,⟨patch_mem6_4_0_10,by simp⟩⟩⟩⟩⟩⟩
theorem row_eq6_4_1_0 : RadiusFivePruning.stateRow6_4_1_0 = ParentOwnership.parentRow0115 := by rfl
theorem patch_mem6_4_1_0 : RadiusFivePruning.patch6_4_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0115, parentRow_mem0115, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0115_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_1_0]
  rfl
theorem row_eq6_4_1_3 : RadiusFivePruning.stateRow6_4_1_3 = ParentOwnership.parentRow0116 := by rfl
theorem patch_mem6_4_1_3 : RadiusFivePruning.patch6_4_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0116, parentRow_mem0116, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0116_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_1_3]
  rfl
theorem row_eq6_4_1_4 : RadiusFivePruning.stateRow6_4_1_4 = ParentOwnership.parentRow0533 := by rfl
theorem patch_mem6_4_1_4 : RadiusFivePruning.patch6_4_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0533, parentRow_mem0533, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0533_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_1_4]
  rfl
theorem row_eq6_4_1_5 : RadiusFivePruning.stateRow6_4_1_5 = ParentOwnership.parentRow0534 := by rfl
theorem patch_mem6_4_1_5 : RadiusFivePruning.patch6_4_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0534, parentRow_mem0534, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0534_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_1_5]
  rfl
theorem row_eq6_4_1_7 : RadiusFivePruning.stateRow6_4_1_7 = ParentOwnership.parentRow0114 := by rfl
theorem patch_mem6_4_1_7 : RadiusFivePruning.patch6_4_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0114, parentRow_mem0114, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0114_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_1_7]
  rfl
theorem row_eq6_4_1_8 : RadiusFivePruning.stateRow6_4_1_8 = ParentOwnership.parentRow0118 := by rfl
theorem patch_mem6_4_1_8 : RadiusFivePruning.patch6_4_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0118, parentRow_mem0118, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0118_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_1_8]
  rfl
theorem row_eq6_4_1_10 : RadiusFivePruning.stateRow6_4_1_10 = ParentOwnership.parentRow0119 := by rfl
theorem patch_mem6_4_1_10 : RadiusFivePruning.patch6_4_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0119, parentRow_mem0119, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0119_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_1_10]
  rfl
theorem row_eq6_4_1_11 : RadiusFivePruning.stateRow6_4_1_11 = ParentOwnership.parentRow1719 := by rfl
theorem patch_mem6_4_1_11 : RadiusFivePruning.patch6_4_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1719, parentRow_mem1719, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1719_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_1_11]
  rfl
theorem chunk_mem6_4_1 : ∀ p ∈ RadiusFivePruning.final6_4_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_4_1, List.forall_mem_cons]
  exact ⟨patch_mem6_4_1_0,⟨patch_mem6_4_1_3,⟨patch_mem6_4_1_4,⟨patch_mem6_4_1_5,⟨patch_mem6_4_1_7,⟨patch_mem6_4_1_8,⟨patch_mem6_4_1_10,⟨patch_mem6_4_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
