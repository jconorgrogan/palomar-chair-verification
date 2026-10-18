module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock6T1C4
public import SpectreFinite.RadiusFivePruningLiteralBlock6T1C5
public import SpectreFinite.RadiusFivePruningLiteralBlock6T2C0
public import SpectreFinite.RadiusFivePruningLiteralBlock6T2C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq6_1_4_0 : RadiusFivePruning.stateRow6_1_4_0 = ParentOwnership.parentRow1335 := by rfl
theorem patch_mem6_1_4_0 : RadiusFivePruning.patch6_1_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1335, parentRow_mem1335, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1335_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_4_0]
  rfl
theorem row_eq6_1_4_1 : RadiusFivePruning.stateRow6_1_4_1 = ParentOwnership.parentRow1327 := by rfl
theorem patch_mem6_1_4_1 : RadiusFivePruning.patch6_1_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1327, parentRow_mem1327, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1327_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_4_1]
  rfl
theorem row_eq6_1_4_2 : RadiusFivePruning.stateRow6_1_4_2 = ParentOwnership.parentRow1328 := by rfl
theorem patch_mem6_1_4_2 : RadiusFivePruning.patch6_1_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1328, parentRow_mem1328, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1328_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_4_2]
  rfl
theorem row_eq6_1_4_3 : RadiusFivePruning.stateRow6_1_4_3 = ParentOwnership.parentRow1319 := by rfl
theorem patch_mem6_1_4_3 : RadiusFivePruning.patch6_1_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1319, parentRow_mem1319, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1319_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_4_3]
  rfl
theorem row_eq6_1_4_4 : RadiusFivePruning.stateRow6_1_4_4 = ParentOwnership.parentRow1321 := by rfl
theorem patch_mem6_1_4_4 : RadiusFivePruning.patch6_1_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1321, parentRow_mem1321, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1321_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_4_4]
  rfl
theorem row_eq6_1_4_5 : RadiusFivePruning.stateRow6_1_4_5 = ParentOwnership.parentRow1320 := by rfl
theorem patch_mem6_1_4_5 : RadiusFivePruning.patch6_1_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1320, parentRow_mem1320, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1320_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_4_5]
  rfl
theorem row_eq6_1_4_6 : RadiusFivePruning.stateRow6_1_4_6 = ParentOwnership.parentRow1322 := by rfl
theorem patch_mem6_1_4_6 : RadiusFivePruning.patch6_1_4_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1322, parentRow_mem1322, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1322_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_4_6]
  rfl
theorem row_eq6_1_4_7 : RadiusFivePruning.stateRow6_1_4_7 = ParentOwnership.parentRow1323 := by rfl
theorem patch_mem6_1_4_7 : RadiusFivePruning.patch6_1_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1323, parentRow_mem1323, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1323_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_4_7]
  rfl
theorem row_eq6_1_4_8 : RadiusFivePruning.stateRow6_1_4_8 = ParentOwnership.parentRow1304 := by rfl
theorem patch_mem6_1_4_8 : RadiusFivePruning.patch6_1_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1304, parentRow_mem1304, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1304_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_4_8]
  rfl
theorem row_eq6_1_4_9 : RadiusFivePruning.stateRow6_1_4_9 = ParentOwnership.parentRow1306 := by rfl
theorem patch_mem6_1_4_9 : RadiusFivePruning.patch6_1_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1306, parentRow_mem1306, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1306_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_4_9]
  rfl
theorem row_eq6_1_4_10 : RadiusFivePruning.stateRow6_1_4_10 = ParentOwnership.parentRow1305 := by rfl
theorem patch_mem6_1_4_10 : RadiusFivePruning.patch6_1_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1305, parentRow_mem1305, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1305_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_4_10]
  rfl
theorem row_eq6_1_4_11 : RadiusFivePruning.stateRow6_1_4_11 = ParentOwnership.parentRow1307 := by rfl
theorem patch_mem6_1_4_11 : RadiusFivePruning.patch6_1_4_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1307, parentRow_mem1307, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1307_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_4_11]
  rfl
theorem chunk_mem6_1_4 : ∀ p ∈ RadiusFivePruning.final6_1_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_1_4, List.forall_mem_cons]
  exact ⟨patch_mem6_1_4_0,⟨patch_mem6_1_4_1,⟨patch_mem6_1_4_2,⟨patch_mem6_1_4_3,⟨patch_mem6_1_4_4,⟨patch_mem6_1_4_5,⟨patch_mem6_1_4_6,⟨patch_mem6_1_4_7,⟨patch_mem6_1_4_8,⟨patch_mem6_1_4_9,⟨patch_mem6_1_4_10,⟨patch_mem6_1_4_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_1_5_0 : RadiusFivePruning.stateRow6_1_5_0 = ParentOwnership.parentRow1308 := by rfl
theorem patch_mem6_1_5_0 : RadiusFivePruning.patch6_1_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1308, parentRow_mem1308, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1308_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_5_0]
  rfl
theorem row_eq6_1_5_1 : RadiusFivePruning.stateRow6_1_5_1 = ParentOwnership.parentRow1314 := by rfl
theorem patch_mem6_1_5_1 : RadiusFivePruning.patch6_1_5_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1314, parentRow_mem1314, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1314_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_5_1]
  rfl
theorem row_eq6_1_5_2 : RadiusFivePruning.stateRow6_1_5_2 = ParentOwnership.parentRow1315 := by rfl
theorem patch_mem6_1_5_2 : RadiusFivePruning.patch6_1_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1315, parentRow_mem1315, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1315_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_5_2]
  rfl
theorem chunk_mem6_1_5 : ∀ p ∈ RadiusFivePruning.final6_1_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_1_5, List.forall_mem_cons]
  exact ⟨patch_mem6_1_5_0,⟨patch_mem6_1_5_1,⟨patch_mem6_1_5_2,by simp⟩⟩⟩
theorem row_eq6_2_0_2 : RadiusFivePruning.stateRow6_2_0_2 = ParentOwnership.parentRow1087 := by rfl
theorem patch_mem6_2_0_2 : RadiusFivePruning.patch6_2_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1087, parentRow_mem1087, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1087_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_0_2]
  rfl
theorem row_eq6_2_0_3 : RadiusFivePruning.stateRow6_2_0_3 = ParentOwnership.parentRow0335 := by rfl
theorem patch_mem6_2_0_3 : RadiusFivePruning.patch6_2_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0335, parentRow_mem0335, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0335_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_0_3]
  rfl
theorem row_eq6_2_0_5 : RadiusFivePruning.stateRow6_2_0_5 = ParentOwnership.parentRow1455 := by rfl
theorem patch_mem6_2_0_5 : RadiusFivePruning.patch6_2_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1455, parentRow_mem1455, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1455_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_0_5]
  rfl
theorem row_eq6_2_0_6 : RadiusFivePruning.stateRow6_2_0_6 = ParentOwnership.parentRow1452 := by rfl
theorem patch_mem6_2_0_6 : RadiusFivePruning.patch6_2_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1452, parentRow_mem1452, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1452_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_0_6]
  rfl
theorem row_eq6_2_0_8 : RadiusFivePruning.stateRow6_2_0_8 = ParentOwnership.parentRow0166 := by rfl
theorem patch_mem6_2_0_8 : RadiusFivePruning.patch6_2_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0166, parentRow_mem0166, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0166_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_0_8]
  rfl
theorem row_eq6_2_0_10 : RadiusFivePruning.stateRow6_2_0_10 = ParentOwnership.parentRow0161 := by rfl
theorem patch_mem6_2_0_10 : RadiusFivePruning.patch6_2_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0161, parentRow_mem0161, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0161_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_0_10]
  rfl
theorem chunk_mem6_2_0 : ∀ p ∈ RadiusFivePruning.final6_2_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_2_0, List.forall_mem_cons]
  exact ⟨patch_mem6_2_0_2,⟨patch_mem6_2_0_3,⟨patch_mem6_2_0_5,⟨patch_mem6_2_0_6,⟨patch_mem6_2_0_8,⟨patch_mem6_2_0_10,by simp⟩⟩⟩⟩⟩⟩
theorem row_eq6_2_1_0 : RadiusFivePruning.stateRow6_2_1_0 = ParentOwnership.parentRow0128 := by rfl
theorem patch_mem6_2_1_0 : RadiusFivePruning.patch6_2_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0128, parentRow_mem0128, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0128_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_1_0]
  rfl
theorem row_eq6_2_1_3 : RadiusFivePruning.stateRow6_2_1_3 = ParentOwnership.parentRow0130 := by rfl
theorem patch_mem6_2_1_3 : RadiusFivePruning.patch6_2_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0130, parentRow_mem0130, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0130_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_1_3]
  rfl
theorem row_eq6_2_1_4 : RadiusFivePruning.stateRow6_2_1_4 = ParentOwnership.parentRow0132 := by rfl
theorem patch_mem6_2_1_4 : RadiusFivePruning.patch6_2_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0132, parentRow_mem0132, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0132_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_1_4]
  rfl
theorem row_eq6_2_1_5 : RadiusFivePruning.stateRow6_2_1_5 = ParentOwnership.parentRow1091 := by rfl
theorem patch_mem6_2_1_5 : RadiusFivePruning.patch6_2_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1091, parentRow_mem1091, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1091_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_1_5]
  rfl
theorem row_eq6_2_1_7 : RadiusFivePruning.stateRow6_2_1_7 = ParentOwnership.parentRow0285 := by rfl
theorem patch_mem6_2_1_7 : RadiusFivePruning.patch6_2_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0285, parentRow_mem0285, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0285_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_1_7]
  rfl
theorem row_eq6_2_1_8 : RadiusFivePruning.stateRow6_2_1_8 = ParentOwnership.parentRow0164 := by rfl
theorem patch_mem6_2_1_8 : RadiusFivePruning.patch6_2_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0164, parentRow_mem0164, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0164_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_1_8]
  rfl
theorem row_eq6_2_1_10 : RadiusFivePruning.stateRow6_2_1_10 = ParentOwnership.parentRow0169 := by rfl
theorem patch_mem6_2_1_10 : RadiusFivePruning.patch6_2_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0169, parentRow_mem0169, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0169_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_1_10]
  rfl
theorem row_eq6_2_1_11 : RadiusFivePruning.stateRow6_2_1_11 = ParentOwnership.parentRow0181 := by rfl
theorem patch_mem6_2_1_11 : RadiusFivePruning.patch6_2_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0181, parentRow_mem0181, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0181_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_1_11]
  rfl
theorem chunk_mem6_2_1 : ∀ p ∈ RadiusFivePruning.final6_2_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_2_1, List.forall_mem_cons]
  exact ⟨patch_mem6_2_1_0,⟨patch_mem6_2_1_3,⟨patch_mem6_2_1_4,⟨patch_mem6_2_1_5,⟨patch_mem6_2_1_7,⟨patch_mem6_2_1_8,⟨patch_mem6_2_1_10,⟨patch_mem6_2_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
