module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock6T2C2
public import SpectreFinite.RadiusFivePruningLiteralBlock6T2C3
public import SpectreFinite.RadiusFivePruningLiteralBlock6T2C4
public import SpectreFinite.RadiusFivePruningLiteralBlock6T2C5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq6_2_2_0 : RadiusFivePruning.stateRow6_2_2_0 = ParentOwnership.parentRow0159 := by rfl
theorem patch_mem6_2_2_0 : RadiusFivePruning.patch6_2_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0159, parentRow_mem0159, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0159_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_2_0]
  rfl
theorem row_eq6_2_2_1 : RadiusFivePruning.stateRow6_2_2_1 = ParentOwnership.parentRow0162 := by rfl
theorem patch_mem6_2_2_1 : RadiusFivePruning.patch6_2_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0162, parentRow_mem0162, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0162_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_2_1]
  rfl
theorem row_eq6_2_2_2 : RadiusFivePruning.stateRow6_2_2_2 = ParentOwnership.parentRow0147 := by rfl
theorem patch_mem6_2_2_2 : RadiusFivePruning.patch6_2_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0147, parentRow_mem0147, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0147_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_2_2]
  rfl
theorem row_eq6_2_2_5 : RadiusFivePruning.stateRow6_2_2_5 = ParentOwnership.parentRow0173 := by rfl
theorem patch_mem6_2_2_5 : RadiusFivePruning.patch6_2_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0173, parentRow_mem0173, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0173_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_2_5]
  rfl
theorem row_eq6_2_2_6 : RadiusFivePruning.stateRow6_2_2_6 = ParentOwnership.parentRow0129 := by rfl
theorem patch_mem6_2_2_6 : RadiusFivePruning.patch6_2_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0129, parentRow_mem0129, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0129_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_2_6]
  rfl
theorem row_eq6_2_2_7 : RadiusFivePruning.stateRow6_2_2_7 = ParentOwnership.parentRow0131 := by rfl
theorem patch_mem6_2_2_7 : RadiusFivePruning.patch6_2_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0131, parentRow_mem0131, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0131_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_2_7]
  rfl
theorem row_eq6_2_2_8 : RadiusFivePruning.stateRow6_2_2_8 = ParentOwnership.parentRow1090 := by rfl
theorem patch_mem6_2_2_8 : RadiusFivePruning.patch6_2_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1090, parentRow_mem1090, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1090_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_2_8]
  rfl
theorem row_eq6_2_2_9 : RadiusFivePruning.stateRow6_2_2_9 = ParentOwnership.parentRow0126 := by rfl
theorem patch_mem6_2_2_9 : RadiusFivePruning.patch6_2_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0126, parentRow_mem0126, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0126_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_2_9]
  rfl
theorem row_eq6_2_2_10 : RadiusFivePruning.stateRow6_2_2_10 = ParentOwnership.parentRow0127 := by rfl
theorem patch_mem6_2_2_10 : RadiusFivePruning.patch6_2_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0127, parentRow_mem0127, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0127_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_2_10]
  rfl
theorem row_eq6_2_2_11 : RadiusFivePruning.stateRow6_2_2_11 = ParentOwnership.parentRow1088 := by rfl
theorem patch_mem6_2_2_11 : RadiusFivePruning.patch6_2_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1088, parentRow_mem1088, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1088_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_2_11]
  rfl
theorem chunk_mem6_2_2 : ∀ p ∈ RadiusFivePruning.final6_2_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_2_2, List.forall_mem_cons]
  exact ⟨patch_mem6_2_2_0,⟨patch_mem6_2_2_1,⟨patch_mem6_2_2_2,⟨patch_mem6_2_2_5,⟨patch_mem6_2_2_6,⟨patch_mem6_2_2_7,⟨patch_mem6_2_2_8,⟨patch_mem6_2_2_9,⟨patch_mem6_2_2_10,⟨patch_mem6_2_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_2_3_0 : RadiusFivePruning.stateRow6_2_3_0 = ParentOwnership.parentRow1089 := by rfl
theorem patch_mem6_2_3_0 : RadiusFivePruning.patch6_2_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1089, parentRow_mem1089, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1089_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_3_0]
  rfl
theorem row_eq6_2_3_1 : RadiusFivePruning.stateRow6_2_3_1 = ParentOwnership.parentRow0299 := by rfl
theorem patch_mem6_2_3_1 : RadiusFivePruning.patch6_2_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0299, parentRow_mem0299, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0299_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_3_1]
  rfl
theorem row_eq6_2_3_4 : RadiusFivePruning.stateRow6_2_3_4 = ParentOwnership.parentRow0305 := by rfl
theorem patch_mem6_2_3_4 : RadiusFivePruning.patch6_2_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0305, parentRow_mem0305, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0305_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_3_4]
  rfl
theorem row_eq6_2_3_5 : RadiusFivePruning.stateRow6_2_3_5 = ParentOwnership.parentRow1060 := by rfl
theorem patch_mem6_2_3_5 : RadiusFivePruning.patch6_2_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1060, parentRow_mem1060, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1060_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_3_5]
  rfl
theorem row_eq6_2_3_6 : RadiusFivePruning.stateRow6_2_3_6 = ParentOwnership.parentRow0297 := by rfl
theorem patch_mem6_2_3_6 : RadiusFivePruning.patch6_2_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0297, parentRow_mem0297, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0297_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_3_6]
  rfl
theorem row_eq6_2_3_7 : RadiusFivePruning.stateRow6_2_3_7 = ParentOwnership.parentRow0306 := by rfl
theorem patch_mem6_2_3_7 : RadiusFivePruning.patch6_2_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0306, parentRow_mem0306, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0306_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_3_7]
  rfl
theorem row_eq6_2_3_8 : RadiusFivePruning.stateRow6_2_3_8 = ParentOwnership.parentRow0298 := by rfl
theorem patch_mem6_2_3_8 : RadiusFivePruning.patch6_2_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0298, parentRow_mem0298, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0298_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_3_8]
  rfl
theorem row_eq6_2_3_9 : RadiusFivePruning.stateRow6_2_3_9 = ParentOwnership.parentRow0307 := by rfl
theorem patch_mem6_2_3_9 : RadiusFivePruning.patch6_2_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0307, parentRow_mem0307, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0307_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_3_9]
  rfl
theorem row_eq6_2_3_10 : RadiusFivePruning.stateRow6_2_3_10 = ParentOwnership.parentRow0284 := by rfl
theorem patch_mem6_2_3_10 : RadiusFivePruning.patch6_2_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0284, parentRow_mem0284, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0284_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_3_10]
  rfl
theorem row_eq6_2_3_11 : RadiusFivePruning.stateRow6_2_3_11 = ParentOwnership.parentRow0286 := by rfl
theorem patch_mem6_2_3_11 : RadiusFivePruning.patch6_2_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0286, parentRow_mem0286, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0286_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_3_11]
  rfl
theorem chunk_mem6_2_3 : ∀ p ∈ RadiusFivePruning.final6_2_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_2_3, List.forall_mem_cons]
  exact ⟨patch_mem6_2_3_0,⟨patch_mem6_2_3_1,⟨patch_mem6_2_3_4,⟨patch_mem6_2_3_5,⟨patch_mem6_2_3_6,⟨patch_mem6_2_3_7,⟨patch_mem6_2_3_8,⟨patch_mem6_2_3_9,⟨patch_mem6_2_3_10,⟨patch_mem6_2_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_2_4_0 : RadiusFivePruning.stateRow6_2_4_0 = ParentOwnership.parentRow1041 := by rfl
theorem patch_mem6_2_4_0 : RadiusFivePruning.patch6_2_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1041, parentRow_mem1041, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1041_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_4_0]
  rfl
theorem row_eq6_2_4_1 : RadiusFivePruning.stateRow6_2_4_1 = ParentOwnership.parentRow0287 := by rfl
theorem patch_mem6_2_4_1 : RadiusFivePruning.patch6_2_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0287, parentRow_mem0287, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0287_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_4_1]
  rfl
theorem row_eq6_2_4_2 : RadiusFivePruning.stateRow6_2_4_2 = ParentOwnership.parentRow0288 := by rfl
theorem patch_mem6_2_4_2 : RadiusFivePruning.patch6_2_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0288, parentRow_mem0288, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0288_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_4_2]
  rfl
theorem row_eq6_2_4_3 : RadiusFivePruning.stateRow6_2_4_3 = ParentOwnership.parentRow0148 := by rfl
theorem patch_mem6_2_4_3 : RadiusFivePruning.patch6_2_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0148, parentRow_mem0148, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0148_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_4_3]
  rfl
theorem row_eq6_2_4_4 : RadiusFivePruning.stateRow6_2_4_4 = ParentOwnership.parentRow0167 := by rfl
theorem patch_mem6_2_4_4 : RadiusFivePruning.patch6_2_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0167, parentRow_mem0167, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0167_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_4_4]
  rfl
theorem row_eq6_2_4_5 : RadiusFivePruning.stateRow6_2_4_5 = ParentOwnership.parentRow0149 := by rfl
theorem patch_mem6_2_4_5 : RadiusFivePruning.patch6_2_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0149, parentRow_mem0149, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0149_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_4_5]
  rfl
theorem row_eq6_2_4_6 : RadiusFivePruning.stateRow6_2_4_6 = ParentOwnership.parentRow0168 := by rfl
theorem patch_mem6_2_4_6 : RadiusFivePruning.patch6_2_4_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0168, parentRow_mem0168, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0168_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_4_6]
  rfl
theorem row_eq6_2_4_7 : RadiusFivePruning.stateRow6_2_4_7 = ParentOwnership.parentRow0165 := by rfl
theorem patch_mem6_2_4_7 : RadiusFivePruning.patch6_2_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0165, parentRow_mem0165, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0165_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_4_7]
  rfl
theorem row_eq6_2_4_8 : RadiusFivePruning.stateRow6_2_4_8 = ParentOwnership.parentRow0157 := by rfl
theorem patch_mem6_2_4_8 : RadiusFivePruning.patch6_2_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0157, parentRow_mem0157, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0157_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_4_8]
  rfl
theorem row_eq6_2_4_9 : RadiusFivePruning.stateRow6_2_4_9 = ParentOwnership.parentRow0171 := by rfl
theorem patch_mem6_2_4_9 : RadiusFivePruning.patch6_2_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0171, parentRow_mem0171, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0171_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_4_9]
  rfl
theorem row_eq6_2_4_10 : RadiusFivePruning.stateRow6_2_4_10 = ParentOwnership.parentRow0158 := by rfl
theorem patch_mem6_2_4_10 : RadiusFivePruning.patch6_2_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0158, parentRow_mem0158, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0158_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_4_10]
  rfl
theorem row_eq6_2_4_11 : RadiusFivePruning.stateRow6_2_4_11 = ParentOwnership.parentRow0172 := by rfl
theorem patch_mem6_2_4_11 : RadiusFivePruning.patch6_2_4_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0172, parentRow_mem0172, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0172_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_4_11]
  rfl
theorem chunk_mem6_2_4 : ∀ p ∈ RadiusFivePruning.final6_2_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_2_4, List.forall_mem_cons]
  exact ⟨patch_mem6_2_4_0,⟨patch_mem6_2_4_1,⟨patch_mem6_2_4_2,⟨patch_mem6_2_4_3,⟨patch_mem6_2_4_4,⟨patch_mem6_2_4_5,⟨patch_mem6_2_4_6,⟨patch_mem6_2_4_7,⟨patch_mem6_2_4_8,⟨patch_mem6_2_4_9,⟨patch_mem6_2_4_10,⟨patch_mem6_2_4_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_2_5_0 : RadiusFivePruning.stateRow6_2_5_0 = ParentOwnership.parentRow0170 := by rfl
theorem patch_mem6_2_5_0 : RadiusFivePruning.patch6_2_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0170, parentRow_mem0170, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0170_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_5_0]
  rfl
theorem row_eq6_2_5_1 : RadiusFivePruning.stateRow6_2_5_1 = ParentOwnership.parentRow0160 := by rfl
theorem patch_mem6_2_5_1 : RadiusFivePruning.patch6_2_5_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0160, parentRow_mem0160, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0160_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_5_1]
  rfl
theorem row_eq6_2_5_2 : RadiusFivePruning.stateRow6_2_5_2 = ParentOwnership.parentRow0163 := by rfl
theorem patch_mem6_2_5_2 : RadiusFivePruning.patch6_2_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0163, parentRow_mem0163, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0163_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_2_5_2]
  rfl
theorem chunk_mem6_2_5 : ∀ p ∈ RadiusFivePruning.final6_2_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_2_5, List.forall_mem_cons]
  exact ⟨patch_mem6_2_5_0,⟨patch_mem6_2_5_1,⟨patch_mem6_2_5_2,by simp⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
