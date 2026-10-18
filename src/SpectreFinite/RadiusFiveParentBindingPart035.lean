module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock6T4C2
public import SpectreFinite.RadiusFivePruningLiteralBlock6T4C3
public import SpectreFinite.RadiusFivePruningLiteralBlock6T4C4
public import SpectreFinite.RadiusFivePruningLiteralBlock6T4C5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq6_4_2_0 : RadiusFivePruning.stateRow6_4_2_0 = ParentOwnership.parentRow0121 := by rfl
theorem patch_mem6_4_2_0 : RadiusFivePruning.patch6_4_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0121, parentRow_mem0121, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0121_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_2_0]
  rfl
theorem row_eq6_4_2_1 : RadiusFivePruning.stateRow6_4_2_1 = ParentOwnership.parentRow0541 := by rfl
theorem patch_mem6_4_2_1 : RadiusFivePruning.patch6_4_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0541, parentRow_mem0541, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0541_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_2_1]
  rfl
theorem row_eq6_4_2_2 : RadiusFivePruning.stateRow6_4_2_2 = ParentOwnership.parentRow0549 := by rfl
theorem patch_mem6_4_2_2 : RadiusFivePruning.patch6_4_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0549, parentRow_mem0549, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0549_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_2_2]
  rfl
theorem row_eq6_4_2_5 : RadiusFivePruning.stateRow6_4_2_5 = ParentOwnership.parentRow0538 := by rfl
theorem patch_mem6_4_2_5 : RadiusFivePruning.patch6_4_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0538, parentRow_mem0538, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0538_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_2_5]
  rfl
theorem row_eq6_4_2_6 : RadiusFivePruning.stateRow6_4_2_6 = ParentOwnership.parentRow0120 := by rfl
theorem patch_mem6_4_2_6 : RadiusFivePruning.patch6_4_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0120, parentRow_mem0120, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0120_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_2_6]
  rfl
theorem row_eq6_4_2_7 : RadiusFivePruning.stateRow6_4_2_7 = ParentOwnership.parentRow0539 := by rfl
theorem patch_mem6_4_2_7 : RadiusFivePruning.patch6_4_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0539, parentRow_mem0539, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0539_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_2_7]
  rfl
theorem row_eq6_4_2_8 : RadiusFivePruning.stateRow6_4_2_8 = ParentOwnership.parentRow0540 := by rfl
theorem patch_mem6_4_2_8 : RadiusFivePruning.patch6_4_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0540, parentRow_mem0540, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0540_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_2_8]
  rfl
theorem row_eq6_4_2_9 : RadiusFivePruning.stateRow6_4_2_9 = ParentOwnership.parentRow0547 := by rfl
theorem patch_mem6_4_2_9 : RadiusFivePruning.patch6_4_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0547, parentRow_mem0547, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0547_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_2_9]
  rfl
theorem row_eq6_4_2_10 : RadiusFivePruning.stateRow6_4_2_10 = ParentOwnership.parentRow0550 := by rfl
theorem patch_mem6_4_2_10 : RadiusFivePruning.patch6_4_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0550, parentRow_mem0550, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0550_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_2_10]
  rfl
theorem row_eq6_4_2_11 : RadiusFivePruning.stateRow6_4_2_11 = ParentOwnership.parentRow0548 := by rfl
theorem patch_mem6_4_2_11 : RadiusFivePruning.patch6_4_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0548, parentRow_mem0548, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0548_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_2_11]
  rfl
theorem chunk_mem6_4_2 : ∀ p ∈ RadiusFivePruning.final6_4_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_4_2, List.forall_mem_cons]
  exact ⟨patch_mem6_4_2_0,⟨patch_mem6_4_2_1,⟨patch_mem6_4_2_2,⟨patch_mem6_4_2_5,⟨patch_mem6_4_2_6,⟨patch_mem6_4_2_7,⟨patch_mem6_4_2_8,⟨patch_mem6_4_2_9,⟨patch_mem6_4_2_10,⟨patch_mem6_4_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_4_3_0 : RadiusFivePruning.stateRow6_4_3_0 = ParentOwnership.parentRow0551 := by rfl
theorem patch_mem6_4_3_0 : RadiusFivePruning.patch6_4_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0551, parentRow_mem0551, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0551_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_3_0]
  rfl
theorem row_eq6_4_3_1 : RadiusFivePruning.stateRow6_4_3_1 = ParentOwnership.parentRow0315 := by rfl
theorem patch_mem6_4_3_1 : RadiusFivePruning.patch6_4_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0315, parentRow_mem0315, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0315_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_3_1]
  rfl
theorem row_eq6_4_3_4 : RadiusFivePruning.stateRow6_4_3_4 = ParentOwnership.parentRow0092 := by rfl
theorem patch_mem6_4_3_4 : RadiusFivePruning.patch6_4_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0092, parentRow_mem0092, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0092_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_3_4]
  rfl
theorem row_eq6_4_3_5 : RadiusFivePruning.stateRow6_4_3_5 = ParentOwnership.parentRow0088 := by rfl
theorem patch_mem6_4_3_5 : RadiusFivePruning.patch6_4_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0088, parentRow_mem0088, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0088_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_3_5]
  rfl
theorem row_eq6_4_3_6 : RadiusFivePruning.stateRow6_4_3_6 = ParentOwnership.parentRow0318 := by rfl
theorem patch_mem6_4_3_6 : RadiusFivePruning.patch6_4_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0318, parentRow_mem0318, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0318_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_3_6]
  rfl
theorem row_eq6_4_3_7 : RadiusFivePruning.stateRow6_4_3_7 = ParentOwnership.parentRow1084 := by rfl
theorem patch_mem6_4_3_7 : RadiusFivePruning.patch6_4_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1084, parentRow_mem1084, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1084_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_3_7]
  rfl
theorem row_eq6_4_3_8 : RadiusFivePruning.stateRow6_4_3_8 = ParentOwnership.parentRow0316 := by rfl
theorem patch_mem6_4_3_8 : RadiusFivePruning.patch6_4_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0316, parentRow_mem0316, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0316_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_3_8]
  rfl
theorem row_eq6_4_3_9 : RadiusFivePruning.stateRow6_4_3_9 = ParentOwnership.parentRow1082 := by rfl
theorem patch_mem6_4_3_9 : RadiusFivePruning.patch6_4_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1082, parentRow_mem1082, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1082_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_3_9]
  rfl
theorem row_eq6_4_3_10 : RadiusFivePruning.stateRow6_4_3_10 = ParentOwnership.parentRow0089 := by rfl
theorem patch_mem6_4_3_10 : RadiusFivePruning.patch6_4_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0089, parentRow_mem0089, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0089_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_3_10]
  rfl
theorem row_eq6_4_3_11 : RadiusFivePruning.stateRow6_4_3_11 = ParentOwnership.parentRow0093 := by rfl
theorem patch_mem6_4_3_11 : RadiusFivePruning.patch6_4_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0093, parentRow_mem0093, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0093_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_3_11]
  rfl
theorem chunk_mem6_4_3 : ∀ p ∈ RadiusFivePruning.final6_4_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_4_3, List.forall_mem_cons]
  exact ⟨patch_mem6_4_3_0,⟨patch_mem6_4_3_1,⟨patch_mem6_4_3_4,⟨patch_mem6_4_3_5,⟨patch_mem6_4_3_6,⟨patch_mem6_4_3_7,⟨patch_mem6_4_3_8,⟨patch_mem6_4_3_9,⟨patch_mem6_4_3_10,⟨patch_mem6_4_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_4_4_0 : RadiusFivePruning.stateRow6_4_4_0 = ParentOwnership.parentRow0090 := by rfl
theorem patch_mem6_4_4_0 : RadiusFivePruning.patch6_4_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0090, parentRow_mem0090, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0090_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_4_0]
  rfl
theorem row_eq6_4_4_1 : RadiusFivePruning.stateRow6_4_4_1 = ParentOwnership.parentRow1085 := by rfl
theorem patch_mem6_4_4_1 : RadiusFivePruning.patch6_4_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1085, parentRow_mem1085, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1085_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_4_1]
  rfl
theorem row_eq6_4_4_2 : RadiusFivePruning.stateRow6_4_4_2 = ParentOwnership.parentRow1083 := by rfl
theorem patch_mem6_4_4_2 : RadiusFivePruning.patch6_4_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1083, parentRow_mem1083, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1083_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_4_2]
  rfl
theorem row_eq6_4_4_3 : RadiusFivePruning.stateRow6_4_4_3 = ParentOwnership.parentRow0094 := by rfl
theorem patch_mem6_4_4_3 : RadiusFivePruning.patch6_4_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0094, parentRow_mem0094, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0094_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_4_3]
  rfl
theorem row_eq6_4_4_4 : RadiusFivePruning.stateRow6_4_4_4 = ParentOwnership.parentRow0096 := by rfl
theorem patch_mem6_4_4_4 : RadiusFivePruning.patch6_4_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0096, parentRow_mem0096, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0096_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_4_4]
  rfl
theorem row_eq6_4_4_5 : RadiusFivePruning.stateRow6_4_4_5 = ParentOwnership.parentRow0098 := by rfl
theorem patch_mem6_4_4_5 : RadiusFivePruning.patch6_4_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0098, parentRow_mem0098, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0098_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_4_5]
  rfl
theorem row_eq6_4_4_6 : RadiusFivePruning.stateRow6_4_4_6 = ParentOwnership.parentRow0100 := by rfl
theorem patch_mem6_4_4_6 : RadiusFivePruning.patch6_4_4_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0100, parentRow_mem0100, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0100_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_4_6]
  rfl
theorem row_eq6_4_4_7 : RadiusFivePruning.stateRow6_4_4_7 = ParentOwnership.parentRow0122 := by rfl
theorem patch_mem6_4_4_7 : RadiusFivePruning.patch6_4_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0122, parentRow_mem0122, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0122_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_4_7]
  rfl
theorem row_eq6_4_4_8 : RadiusFivePruning.stateRow6_4_4_8 = ParentOwnership.parentRow0095 := by rfl
theorem patch_mem6_4_4_8 : RadiusFivePruning.patch6_4_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0095, parentRow_mem0095, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0095_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_4_8]
  rfl
theorem row_eq6_4_4_9 : RadiusFivePruning.stateRow6_4_4_9 = ParentOwnership.parentRow0097 := by rfl
theorem patch_mem6_4_4_9 : RadiusFivePruning.patch6_4_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0097, parentRow_mem0097, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0097_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_4_9]
  rfl
theorem row_eq6_4_4_10 : RadiusFivePruning.stateRow6_4_4_10 = ParentOwnership.parentRow0099 := by rfl
theorem patch_mem6_4_4_10 : RadiusFivePruning.patch6_4_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0099, parentRow_mem0099, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0099_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_4_10]
  rfl
theorem row_eq6_4_4_11 : RadiusFivePruning.stateRow6_4_4_11 = ParentOwnership.parentRow0101 := by rfl
theorem patch_mem6_4_4_11 : RadiusFivePruning.patch6_4_4_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0101, parentRow_mem0101, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0101_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_4_11]
  rfl
theorem chunk_mem6_4_4 : ∀ p ∈ RadiusFivePruning.final6_4_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_4_4, List.forall_mem_cons]
  exact ⟨patch_mem6_4_4_0,⟨patch_mem6_4_4_1,⟨patch_mem6_4_4_2,⟨patch_mem6_4_4_3,⟨patch_mem6_4_4_4,⟨patch_mem6_4_4_5,⟨patch_mem6_4_4_6,⟨patch_mem6_4_4_7,⟨patch_mem6_4_4_8,⟨patch_mem6_4_4_9,⟨patch_mem6_4_4_10,⟨patch_mem6_4_4_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_4_5_0 : RadiusFivePruning.stateRow6_4_5_0 = ParentOwnership.parentRow0123 := by rfl
theorem patch_mem6_4_5_0 : RadiusFivePruning.patch6_4_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0123, parentRow_mem0123, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0123_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_5_0]
  rfl
theorem row_eq6_4_5_1 : RadiusFivePruning.stateRow6_4_5_1 = ParentOwnership.parentRow0124 := by rfl
theorem patch_mem6_4_5_1 : RadiusFivePruning.patch6_4_5_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0124, parentRow_mem0124, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0124_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_5_1]
  rfl
theorem row_eq6_4_5_2 : RadiusFivePruning.stateRow6_4_5_2 = ParentOwnership.parentRow0542 := by rfl
theorem patch_mem6_4_5_2 : RadiusFivePruning.patch6_4_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0542, parentRow_mem0542, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0542_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_4_5_2]
  rfl
theorem chunk_mem6_4_5 : ∀ p ∈ RadiusFivePruning.final6_4_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_4_5, List.forall_mem_cons]
  exact ⟨patch_mem6_4_5_0,⟨patch_mem6_4_5_1,⟨patch_mem6_4_5_2,by simp⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
