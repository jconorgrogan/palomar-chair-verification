module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock8T5C2
public import SpectreFinite.RadiusFivePruningLiteralBlock8T5C3
public import SpectreFinite.RadiusFivePruningLiteralBlock8T5C4
public import SpectreFinite.RadiusFivePruningLiteralBlock8T5C5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq8_5_2_0 : RadiusFivePruning.stateRow8_5_2_0 = ParentOwnership.parentRow0424 := by rfl
theorem patch_mem8_5_2_0 : RadiusFivePruning.patch8_5_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0424, parentRow_mem0424, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0424_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_2_0]
  rfl
theorem row_eq8_5_2_2 : RadiusFivePruning.stateRow8_5_2_2 = ParentOwnership.parentRow0426 := by rfl
theorem patch_mem8_5_2_2 : RadiusFivePruning.patch8_5_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0426, parentRow_mem0426, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0426_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_2_2]
  rfl
theorem row_eq8_5_2_3 : RadiusFivePruning.stateRow8_5_2_3 = ParentOwnership.parentRow0427 := by rfl
theorem patch_mem8_5_2_3 : RadiusFivePruning.patch8_5_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0427, parentRow_mem0427, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0427_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_2_3]
  rfl
theorem row_eq8_5_2_4 : RadiusFivePruning.stateRow8_5_2_4 = ParentOwnership.parentRow1542 := by rfl
theorem patch_mem8_5_2_4 : RadiusFivePruning.patch8_5_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1542, parentRow_mem1542, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1542_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_2_4]
  rfl
theorem row_eq8_5_2_5 : RadiusFivePruning.stateRow8_5_2_5 = ParentOwnership.parentRow1543 := by rfl
theorem patch_mem8_5_2_5 : RadiusFivePruning.patch8_5_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1543, parentRow_mem1543, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1543_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_2_5]
  rfl
theorem row_eq8_5_2_6 : RadiusFivePruning.stateRow8_5_2_6 = ParentOwnership.parentRow1135 := by rfl
theorem patch_mem8_5_2_6 : RadiusFivePruning.patch8_5_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1135, parentRow_mem1135, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1135_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_2_6]
  rfl
theorem row_eq8_5_2_7 : RadiusFivePruning.stateRow8_5_2_7 = ParentOwnership.parentRow1136 := by rfl
theorem patch_mem8_5_2_7 : RadiusFivePruning.patch8_5_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1136, parentRow_mem1136, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1136_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_2_7]
  rfl
theorem row_eq8_5_2_8 : RadiusFivePruning.stateRow8_5_2_8 = ParentOwnership.parentRow0259 := by rfl
theorem patch_mem8_5_2_8 : RadiusFivePruning.patch8_5_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0259, parentRow_mem0259, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0259_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_2_8]
  rfl
theorem row_eq8_5_2_9 : RadiusFivePruning.stateRow8_5_2_9 = ParentOwnership.parentRow0261 := by rfl
theorem patch_mem8_5_2_9 : RadiusFivePruning.patch8_5_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0261, parentRow_mem0261, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0261_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_2_9]
  rfl
theorem row_eq8_5_2_10 : RadiusFivePruning.stateRow8_5_2_10 = ParentOwnership.parentRow0260 := by rfl
theorem patch_mem8_5_2_10 : RadiusFivePruning.patch8_5_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0260, parentRow_mem0260, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0260_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_2_10]
  rfl
theorem row_eq8_5_2_11 : RadiusFivePruning.stateRow8_5_2_11 = ParentOwnership.parentRow0262 := by rfl
theorem patch_mem8_5_2_11 : RadiusFivePruning.patch8_5_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0262, parentRow_mem0262, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0262_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_2_11]
  rfl
theorem chunk_mem8_5_2 : ∀ p ∈ RadiusFivePruning.final8_5_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_5_2, List.forall_mem_cons]
  exact ⟨patch_mem8_5_2_0,⟨patch_mem8_5_2_2,⟨patch_mem8_5_2_3,⟨patch_mem8_5_2_4,⟨patch_mem8_5_2_5,⟨patch_mem8_5_2_6,⟨patch_mem8_5_2_7,⟨patch_mem8_5_2_8,⟨patch_mem8_5_2_9,⟨patch_mem8_5_2_10,⟨patch_mem8_5_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_5_3_0 : RadiusFivePruning.stateRow8_5_3_0 = ParentOwnership.parentRow0231 := by rfl
theorem patch_mem8_5_3_0 : RadiusFivePruning.patch8_5_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0231, parentRow_mem0231, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0231_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_3_0]
  rfl
theorem row_eq8_5_3_1 : RadiusFivePruning.stateRow8_5_3_1 = ParentOwnership.parentRow0232 := by rfl
theorem patch_mem8_5_3_1 : RadiusFivePruning.patch8_5_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0232, parentRow_mem0232, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0232_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_3_1]
  rfl
theorem row_eq8_5_3_3 : RadiusFivePruning.stateRow8_5_3_3 = ParentOwnership.parentRow0233 := by rfl
theorem patch_mem8_5_3_3 : RadiusFivePruning.patch8_5_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0233, parentRow_mem0233, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0233_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_3_3]
  rfl
theorem row_eq8_5_3_4 : RadiusFivePruning.stateRow8_5_3_4 = ParentOwnership.parentRow0234 := by rfl
theorem patch_mem8_5_3_4 : RadiusFivePruning.patch8_5_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0234, parentRow_mem0234, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0234_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_3_4]
  rfl
theorem row_eq8_5_3_5 : RadiusFivePruning.stateRow8_5_3_5 = ParentOwnership.parentRow0235 := by rfl
theorem patch_mem8_5_3_5 : RadiusFivePruning.patch8_5_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0235, parentRow_mem0235, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0235_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_3_5]
  rfl
theorem row_eq8_5_3_6 : RadiusFivePruning.stateRow8_5_3_6 = ParentOwnership.parentRow0236 := by rfl
theorem patch_mem8_5_3_6 : RadiusFivePruning.patch8_5_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0236, parentRow_mem0236, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0236_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_3_6]
  rfl
theorem row_eq8_5_3_7 : RadiusFivePruning.stateRow8_5_3_7 = ParentOwnership.parentRow1183 := by rfl
theorem patch_mem8_5_3_7 : RadiusFivePruning.patch8_5_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1183, parentRow_mem1183, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1183_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_3_7]
  rfl
theorem row_eq8_5_3_8 : RadiusFivePruning.stateRow8_5_3_8 = ParentOwnership.parentRow1184 := by rfl
theorem patch_mem8_5_3_8 : RadiusFivePruning.patch8_5_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1184, parentRow_mem1184, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1184_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_3_8]
  rfl
theorem row_eq8_5_3_9 : RadiusFivePruning.stateRow8_5_3_9 = ParentOwnership.parentRow1185 := by rfl
theorem patch_mem8_5_3_9 : RadiusFivePruning.patch8_5_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1185, parentRow_mem1185, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1185_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_3_9]
  rfl
theorem row_eq8_5_3_10 : RadiusFivePruning.stateRow8_5_3_10 = ParentOwnership.parentRow1186 := by rfl
theorem patch_mem8_5_3_10 : RadiusFivePruning.patch8_5_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1186, parentRow_mem1186, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1186_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_3_10]
  rfl
theorem row_eq8_5_3_11 : RadiusFivePruning.stateRow8_5_3_11 = ParentOwnership.parentRow1187 := by rfl
theorem patch_mem8_5_3_11 : RadiusFivePruning.patch8_5_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1187, parentRow_mem1187, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1187_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_3_11]
  rfl
theorem chunk_mem8_5_3 : ∀ p ∈ RadiusFivePruning.final8_5_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_5_3, List.forall_mem_cons]
  exact ⟨patch_mem8_5_3_0,⟨patch_mem8_5_3_1,⟨patch_mem8_5_3_3,⟨patch_mem8_5_3_4,⟨patch_mem8_5_3_5,⟨patch_mem8_5_3_6,⟨patch_mem8_5_3_7,⟨patch_mem8_5_3_8,⟨patch_mem8_5_3_9,⟨patch_mem8_5_3_10,⟨patch_mem8_5_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_5_4_0 : RadiusFivePruning.stateRow8_5_4_0 = ParentOwnership.parentRow1188 := by rfl
theorem patch_mem8_5_4_0 : RadiusFivePruning.patch8_5_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1188, parentRow_mem1188, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1188_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_4_0]
  rfl
theorem row_eq8_5_4_1 : RadiusFivePruning.stateRow8_5_4_1 = ParentOwnership.parentRow0239 := by rfl
theorem patch_mem8_5_4_1 : RadiusFivePruning.patch8_5_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0239, parentRow_mem0239, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0239_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_4_1]
  rfl
theorem row_eq8_5_4_2 : RadiusFivePruning.stateRow8_5_4_2 = ParentOwnership.parentRow0241 := by rfl
theorem patch_mem8_5_4_2 : RadiusFivePruning.patch8_5_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0241, parentRow_mem0241, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0241_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_4_2]
  rfl
theorem row_eq8_5_4_3 : RadiusFivePruning.stateRow8_5_4_3 = ParentOwnership.parentRow0247 := by rfl
theorem patch_mem8_5_4_3 : RadiusFivePruning.patch8_5_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0247, parentRow_mem0247, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0247_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_4_3]
  rfl
theorem row_eq8_5_4_4 : RadiusFivePruning.stateRow8_5_4_4 = ParentOwnership.parentRow0248 := by rfl
theorem patch_mem8_5_4_4 : RadiusFivePruning.patch8_5_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0248, parentRow_mem0248, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0248_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_4_4]
  rfl
theorem row_eq8_5_4_5 : RadiusFivePruning.stateRow8_5_4_5 = ParentOwnership.parentRow0272 := by rfl
theorem patch_mem8_5_4_5 : RadiusFivePruning.patch8_5_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0272, parentRow_mem0272, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0272_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_4_5]
  rfl
theorem row_eq8_5_4_8 : RadiusFivePruning.stateRow8_5_4_8 = ParentOwnership.parentRow0271 := by rfl
theorem patch_mem8_5_4_8 : RadiusFivePruning.patch8_5_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0271, parentRow_mem0271, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0271_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_4_8]
  rfl
theorem row_eq8_5_4_9 : RadiusFivePruning.stateRow8_5_4_9 = ParentOwnership.parentRow0273 := by rfl
theorem patch_mem8_5_4_9 : RadiusFivePruning.patch8_5_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0273, parentRow_mem0273, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0273_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_4_9]
  rfl
theorem row_eq8_5_4_10 : RadiusFivePruning.stateRow8_5_4_10 = ParentOwnership.parentRow0275 := by rfl
theorem patch_mem8_5_4_10 : RadiusFivePruning.patch8_5_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0275, parentRow_mem0275, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0275_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_4_10]
  rfl
theorem row_eq8_5_4_11 : RadiusFivePruning.stateRow8_5_4_11 = ParentOwnership.parentRow0274 := by rfl
theorem patch_mem8_5_4_11 : RadiusFivePruning.patch8_5_4_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0274, parentRow_mem0274, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0274_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_4_11]
  rfl
theorem chunk_mem8_5_4 : ∀ p ∈ RadiusFivePruning.final8_5_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_5_4, List.forall_mem_cons]
  exact ⟨patch_mem8_5_4_0,⟨patch_mem8_5_4_1,⟨patch_mem8_5_4_2,⟨patch_mem8_5_4_3,⟨patch_mem8_5_4_4,⟨patch_mem8_5_4_5,⟨patch_mem8_5_4_8,⟨patch_mem8_5_4_9,⟨patch_mem8_5_4_10,⟨patch_mem8_5_4_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_5_5_0 : RadiusFivePruning.stateRow8_5_5_0 = ParentOwnership.parentRow0276 := by rfl
theorem patch_mem8_5_5_0 : RadiusFivePruning.patch8_5_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0276, parentRow_mem0276, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0276_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_5_0]
  rfl
theorem row_eq8_5_5_1 : RadiusFivePruning.stateRow8_5_5_1 = ParentOwnership.parentRow0240 := by rfl
theorem patch_mem8_5_5_1 : RadiusFivePruning.patch8_5_5_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0240, parentRow_mem0240, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0240_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_5_1]
  rfl
theorem row_eq8_5_5_2 : RadiusFivePruning.stateRow8_5_5_2 = ParentOwnership.parentRow0242 := by rfl
theorem patch_mem8_5_5_2 : RadiusFivePruning.patch8_5_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0242, parentRow_mem0242, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0242_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_5_2]
  rfl
theorem row_eq8_5_5_3 : RadiusFivePruning.stateRow8_5_5_3 = ParentOwnership.parentRow0243 := by rfl
theorem patch_mem8_5_5_3 : RadiusFivePruning.patch8_5_5_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0243, parentRow_mem0243, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0243_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_5_3]
  rfl
theorem row_eq8_5_5_4 : RadiusFivePruning.stateRow8_5_5_4 = ParentOwnership.parentRow0250 := by rfl
theorem patch_mem8_5_5_4 : RadiusFivePruning.patch8_5_5_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0250, parentRow_mem0250, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0250_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_5_4]
  rfl
theorem row_eq8_5_5_5 : RadiusFivePruning.stateRow8_5_5_5 = ParentOwnership.parentRow0251 := by rfl
theorem patch_mem8_5_5_5 : RadiusFivePruning.patch8_5_5_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0251, parentRow_mem0251, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0251_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_5_5]
  rfl
theorem row_eq8_5_5_6 : RadiusFivePruning.stateRow8_5_5_6 = ParentOwnership.parentRow0252 := by rfl
theorem patch_mem8_5_5_6 : RadiusFivePruning.patch8_5_5_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0252, parentRow_mem0252, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0252_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_5_6]
  rfl
theorem row_eq8_5_5_7 : RadiusFivePruning.stateRow8_5_5_7 = ParentOwnership.parentRow0253 := by rfl
theorem patch_mem8_5_5_7 : RadiusFivePruning.patch8_5_5_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0253, parentRow_mem0253, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0253_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_5_7]
  rfl
theorem row_eq8_5_5_8 : RadiusFivePruning.stateRow8_5_5_8 = ParentOwnership.parentRow0254 := by rfl
theorem patch_mem8_5_5_8 : RadiusFivePruning.patch8_5_5_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0254, parentRow_mem0254, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0254_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_5_8]
  rfl
theorem row_eq8_5_5_9 : RadiusFivePruning.stateRow8_5_5_9 = ParentOwnership.parentRow0255 := by rfl
theorem patch_mem8_5_5_9 : RadiusFivePruning.patch8_5_5_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0255, parentRow_mem0255, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0255_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_5_9]
  rfl
theorem chunk_mem8_5_5 : ∀ p ∈ RadiusFivePruning.final8_5_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_5_5, List.forall_mem_cons]
  exact ⟨patch_mem8_5_5_0,⟨patch_mem8_5_5_1,⟨patch_mem8_5_5_2,⟨patch_mem8_5_5_3,⟨patch_mem8_5_5_4,⟨patch_mem8_5_5_5,⟨patch_mem8_5_5_6,⟨patch_mem8_5_5_7,⟨patch_mem8_5_5_8,⟨patch_mem8_5_5_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
