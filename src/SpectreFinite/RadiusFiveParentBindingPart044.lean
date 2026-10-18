module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock7T2C8
public import SpectreFinite.RadiusFivePruningLiteralBlock7T3C0
public import SpectreFinite.RadiusFivePruningLiteralBlock7T3C1
public import SpectreFinite.RadiusFivePruningLiteralBlock7T3C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq7_2_8_0 : RadiusFivePruning.stateRow7_2_8_0 = ParentOwnership.parentRow1092 := by rfl
theorem patch_mem7_2_8_0 : RadiusFivePruning.patch7_2_8_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1092, parentRow_mem1092, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1092_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_8_0]
  rfl
theorem row_eq7_2_8_1 : RadiusFivePruning.stateRow7_2_8_1 = ParentOwnership.parentRow0347 := by rfl
theorem patch_mem7_2_8_1 : RadiusFivePruning.patch7_2_8_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0347, parentRow_mem0347, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0347_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_8_1]
  rfl
theorem row_eq7_2_8_2 : RadiusFivePruning.stateRow7_2_8_2 = ParentOwnership.parentRow0353 := by rfl
theorem patch_mem7_2_8_2 : RadiusFivePruning.patch7_2_8_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0353, parentRow_mem0353, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0353_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_8_2]
  rfl
theorem row_eq7_2_8_3 : RadiusFivePruning.stateRow7_2_8_3 = ParentOwnership.parentRow0346 := by rfl
theorem patch_mem7_2_8_3 : RadiusFivePruning.patch7_2_8_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0346, parentRow_mem0346, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0346_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_8_3]
  rfl
theorem row_eq7_2_8_5 : RadiusFivePruning.stateRow7_2_8_5 = ParentOwnership.parentRow0216 := by rfl
theorem patch_mem7_2_8_5 : RadiusFivePruning.patch7_2_8_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0216, parentRow_mem0216, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0216_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_8_5]
  rfl
theorem row_eq7_2_8_7 : RadiusFivePruning.stateRow7_2_8_7 = ParentOwnership.parentRow0202 := by rfl
theorem patch_mem7_2_8_7 : RadiusFivePruning.patch7_2_8_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0202, parentRow_mem0202, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0202_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_8_7]
  rfl
theorem row_eq7_2_8_8 : RadiusFivePruning.stateRow7_2_8_8 = ParentOwnership.parentRow0217 := by rfl
theorem patch_mem7_2_8_8 : RadiusFivePruning.patch7_2_8_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0217, parentRow_mem0217, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0217_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_8_8]
  rfl
theorem row_eq7_2_8_9 : RadiusFivePruning.stateRow7_2_8_9 = ParentOwnership.parentRow0218 := by rfl
theorem patch_mem7_2_8_9 : RadiusFivePruning.patch7_2_8_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0218, parentRow_mem0218, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0218_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_8_9]
  rfl
theorem chunk_mem7_2_8 : ∀ p ∈ RadiusFivePruning.final7_2_8, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_2_8, List.forall_mem_cons]
  exact ⟨patch_mem7_2_8_0,⟨patch_mem7_2_8_1,⟨patch_mem7_2_8_2,⟨patch_mem7_2_8_3,⟨patch_mem7_2_8_5,⟨patch_mem7_2_8_7,⟨patch_mem7_2_8_8,⟨patch_mem7_2_8_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_3_0_1 : RadiusFivePruning.stateRow7_3_0_1 = ParentOwnership.parentRow1217 := by rfl
theorem patch_mem7_3_0_1 : RadiusFivePruning.patch7_3_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1217, parentRow_mem1217, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1217_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_0_1]
  rfl
theorem row_eq7_3_0_2 : RadiusFivePruning.stateRow7_3_0_2 = ParentOwnership.parentRow1176 := by rfl
theorem patch_mem7_3_0_2 : RadiusFivePruning.patch7_3_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1176, parentRow_mem1176, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1176_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_0_2]
  rfl
theorem row_eq7_3_0_3 : RadiusFivePruning.stateRow7_3_0_3 = ParentOwnership.parentRow1180 := by rfl
theorem patch_mem7_3_0_3 : RadiusFivePruning.patch7_3_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1180, parentRow_mem1180, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1180_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_0_3]
  rfl
theorem row_eq7_3_0_4 : RadiusFivePruning.stateRow7_3_0_4 = ParentOwnership.parentRow1190 := by rfl
theorem patch_mem7_3_0_4 : RadiusFivePruning.patch7_3_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1190, parentRow_mem1190, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1190_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_0_4]
  rfl
theorem row_eq7_3_0_5 : RadiusFivePruning.stateRow7_3_0_5 = ParentOwnership.parentRow1199 := by rfl
theorem patch_mem7_3_0_5 : RadiusFivePruning.patch7_3_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1199, parentRow_mem1199, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1199_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_0_5]
  rfl
theorem row_eq7_3_0_6 : RadiusFivePruning.stateRow7_3_0_6 = ParentOwnership.parentRow1192 := by rfl
theorem patch_mem7_3_0_6 : RadiusFivePruning.patch7_3_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1192, parentRow_mem1192, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1192_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_0_6]
  rfl
theorem row_eq7_3_0_7 : RadiusFivePruning.stateRow7_3_0_7 = ParentOwnership.parentRow1201 := by rfl
theorem patch_mem7_3_0_7 : RadiusFivePruning.patch7_3_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1201, parentRow_mem1201, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1201_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_0_7]
  rfl
theorem row_eq7_3_0_8 : RadiusFivePruning.stateRow7_3_0_8 = ParentOwnership.parentRow1172 := by rfl
theorem patch_mem7_3_0_8 : RadiusFivePruning.patch7_3_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1172, parentRow_mem1172, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1172_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_0_8]
  rfl
theorem row_eq7_3_0_11 : RadiusFivePruning.stateRow7_3_0_11 = ParentOwnership.parentRow0026 := by rfl
theorem patch_mem7_3_0_11 : RadiusFivePruning.patch7_3_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0026, parentRow_mem0026, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0026_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_0_11]
  rfl
theorem chunk_mem7_3_0 : ∀ p ∈ RadiusFivePruning.final7_3_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_3_0, List.forall_mem_cons]
  exact ⟨patch_mem7_3_0_1,⟨patch_mem7_3_0_2,⟨patch_mem7_3_0_3,⟨patch_mem7_3_0_4,⟨patch_mem7_3_0_5,⟨patch_mem7_3_0_6,⟨patch_mem7_3_0_7,⟨patch_mem7_3_0_8,⟨patch_mem7_3_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_3_1_0 : RadiusFivePruning.stateRow7_3_1_0 = ParentOwnership.parentRow0030 := by rfl
theorem patch_mem7_3_1_0 : RadiusFivePruning.patch7_3_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0030, parentRow_mem0030, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0030_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_1_0]
  rfl
theorem row_eq7_3_1_2 : RadiusFivePruning.stateRow7_3_1_2 = ParentOwnership.parentRow1177 := by rfl
theorem patch_mem7_3_1_2 : RadiusFivePruning.patch7_3_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1177, parentRow_mem1177, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1177_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_1_2]
  rfl
theorem row_eq7_3_1_3 : RadiusFivePruning.stateRow7_3_1_3 = ParentOwnership.parentRow0021 := by rfl
theorem patch_mem7_3_1_3 : RadiusFivePruning.patch7_3_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0021, parentRow_mem0021, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0021_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_1_3]
  rfl
theorem row_eq7_3_1_4 : RadiusFivePruning.stateRow7_3_1_4 = ParentOwnership.parentRow1181 := by rfl
theorem patch_mem7_3_1_4 : RadiusFivePruning.patch7_3_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1181, parentRow_mem1181, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1181_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_1_4]
  rfl
theorem row_eq7_3_1_5 : RadiusFivePruning.stateRow7_3_1_5 = ParentOwnership.parentRow0027 := by rfl
theorem patch_mem7_3_1_5 : RadiusFivePruning.patch7_3_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0027, parentRow_mem0027, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0027_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_1_5]
  rfl
theorem row_eq7_3_1_6 : RadiusFivePruning.stateRow7_3_1_6 = ParentOwnership.parentRow1173 := by rfl
theorem patch_mem7_3_1_6 : RadiusFivePruning.patch7_3_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1173, parentRow_mem1173, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1173_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_1_6]
  rfl
theorem row_eq7_3_1_9 : RadiusFivePruning.stateRow7_3_1_9 = ParentOwnership.parentRow1174 := by rfl
theorem patch_mem7_3_1_9 : RadiusFivePruning.patch7_3_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1174, parentRow_mem1174, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1174_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_1_9]
  rfl
theorem row_eq7_3_1_10 : RadiusFivePruning.stateRow7_3_1_10 = ParentOwnership.parentRow0019 := by rfl
theorem patch_mem7_3_1_10 : RadiusFivePruning.patch7_3_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0019, parentRow_mem0019, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0019_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_1_10]
  rfl
theorem row_eq7_3_1_11 : RadiusFivePruning.stateRow7_3_1_11 = ParentOwnership.parentRow0031 := by rfl
theorem patch_mem7_3_1_11 : RadiusFivePruning.patch7_3_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0031, parentRow_mem0031, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0031_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_1_11]
  rfl
theorem chunk_mem7_3_1 : ∀ p ∈ RadiusFivePruning.final7_3_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_3_1, List.forall_mem_cons]
  exact ⟨patch_mem7_3_1_0,⟨patch_mem7_3_1_2,⟨patch_mem7_3_1_3,⟨patch_mem7_3_1_4,⟨patch_mem7_3_1_5,⟨patch_mem7_3_1_6,⟨patch_mem7_3_1_9,⟨patch_mem7_3_1_10,⟨patch_mem7_3_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_3_2_0 : RadiusFivePruning.stateRow7_3_2_0 = ParentOwnership.parentRow0033 := by rfl
theorem patch_mem7_3_2_0 : RadiusFivePruning.patch7_3_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0033, parentRow_mem0033, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0033_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_2_0]
  rfl
theorem row_eq7_3_2_1 : RadiusFivePruning.stateRow7_3_2_1 = ParentOwnership.parentRow1178 := by rfl
theorem patch_mem7_3_2_1 : RadiusFivePruning.patch7_3_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1178, parentRow_mem1178, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1178_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_2_1]
  rfl
theorem row_eq7_3_2_2 : RadiusFivePruning.stateRow7_3_2_2 = ParentOwnership.parentRow0022 := by rfl
theorem patch_mem7_3_2_2 : RadiusFivePruning.patch7_3_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0022, parentRow_mem0022, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0022_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_2_2]
  rfl
theorem row_eq7_3_2_3 : RadiusFivePruning.stateRow7_3_2_3 = ParentOwnership.parentRow0020 := by rfl
theorem patch_mem7_3_2_3 : RadiusFivePruning.patch7_3_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0020, parentRow_mem0020, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0020_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_2_3]
  rfl
theorem row_eq7_3_2_4 : RadiusFivePruning.stateRow7_3_2_4 = ParentOwnership.parentRow0032 := by rfl
theorem patch_mem7_3_2_4 : RadiusFivePruning.patch7_3_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0032, parentRow_mem0032, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0032_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_2_4]
  rfl
theorem row_eq7_3_2_5 : RadiusFivePruning.stateRow7_3_2_5 = ParentOwnership.parentRow0034 := by rfl
theorem patch_mem7_3_2_5 : RadiusFivePruning.patch7_3_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0034, parentRow_mem0034, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0034_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_2_5]
  rfl
theorem row_eq7_3_2_6 : RadiusFivePruning.stateRow7_3_2_6 = ParentOwnership.parentRow0023 := by rfl
theorem patch_mem7_3_2_6 : RadiusFivePruning.patch7_3_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0023, parentRow_mem0023, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0023_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_2_6]
  rfl
theorem row_eq7_3_2_8 : RadiusFivePruning.stateRow7_3_2_8 = ParentOwnership.parentRow1170 := by rfl
theorem patch_mem7_3_2_8 : RadiusFivePruning.patch7_3_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1170, parentRow_mem1170, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1170_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_2_8]
  rfl
theorem row_eq7_3_2_10 : RadiusFivePruning.stateRow7_3_2_10 = ParentOwnership.parentRow1175 := by rfl
theorem patch_mem7_3_2_10 : RadiusFivePruning.patch7_3_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1175, parentRow_mem1175, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1175_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_2_10]
  rfl
theorem row_eq7_3_2_11 : RadiusFivePruning.stateRow7_3_2_11 = ParentOwnership.parentRow1179 := by rfl
theorem patch_mem7_3_2_11 : RadiusFivePruning.patch7_3_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1179, parentRow_mem1179, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1179_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_2_11]
  rfl
theorem chunk_mem7_3_2 : ∀ p ∈ RadiusFivePruning.final7_3_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_3_2, List.forall_mem_cons]
  exact ⟨patch_mem7_3_2_0,⟨patch_mem7_3_2_1,⟨patch_mem7_3_2_2,⟨patch_mem7_3_2_3,⟨patch_mem7_3_2_4,⟨patch_mem7_3_2_5,⟨patch_mem7_3_2_6,⟨patch_mem7_3_2_8,⟨patch_mem7_3_2_10,⟨patch_mem7_3_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
