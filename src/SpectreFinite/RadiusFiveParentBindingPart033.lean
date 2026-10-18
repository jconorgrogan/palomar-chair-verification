module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock6T3C0
public import SpectreFinite.RadiusFivePruningLiteralBlock6T3C1
public import SpectreFinite.RadiusFivePruningLiteralBlock6T3C2
public import SpectreFinite.RadiusFivePruningLiteralBlock6T3C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq6_3_0_2 : RadiusFivePruning.stateRow6_3_0_2 = ParentOwnership.parentRow0145 := by rfl
theorem patch_mem6_3_0_2 : RadiusFivePruning.patch6_3_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0145, parentRow_mem0145, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0145_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_0_2]
  rfl
theorem row_eq6_3_0_3 : RadiusFivePruning.stateRow6_3_0_3 = ParentOwnership.parentRow0144 := by rfl
theorem patch_mem6_3_0_3 : RadiusFivePruning.patch6_3_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0144, parentRow_mem0144, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0144_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_0_3]
  rfl
theorem row_eq6_3_0_5 : RadiusFivePruning.stateRow6_3_0_5 = ParentOwnership.parentRow1104 := by rfl
theorem patch_mem6_3_0_5 : RadiusFivePruning.patch6_3_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1104, parentRow_mem1104, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1104_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_0_5]
  rfl
theorem row_eq6_3_0_6 : RadiusFivePruning.stateRow6_3_0_6 = ParentOwnership.parentRow0201 := by rfl
theorem patch_mem6_3_0_6 : RadiusFivePruning.patch6_3_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0201, parentRow_mem0201, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0201_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_0_6]
  rfl
theorem row_eq6_3_0_8 : RadiusFivePruning.stateRow6_3_0_8 = ParentOwnership.parentRow1066 := by rfl
theorem patch_mem6_3_0_8 : RadiusFivePruning.patch6_3_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1066, parentRow_mem1066, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1066_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_0_8]
  rfl
theorem row_eq6_3_0_10 : RadiusFivePruning.stateRow6_3_0_10 = ParentOwnership.parentRow1050 := by rfl
theorem patch_mem6_3_0_10 : RadiusFivePruning.patch6_3_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1050, parentRow_mem1050, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1050_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_0_10]
  rfl
theorem chunk_mem6_3_0 : ∀ p ∈ RadiusFivePruning.final6_3_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_3_0, List.forall_mem_cons]
  exact ⟨patch_mem6_3_0_2,⟨patch_mem6_3_0_3,⟨patch_mem6_3_0_5,⟨patch_mem6_3_0_6,⟨patch_mem6_3_0_8,⟨patch_mem6_3_0_10,by simp⟩⟩⟩⟩⟩⟩
theorem row_eq6_3_1_0 : RadiusFivePruning.stateRow6_3_1_0 = ParentOwnership.parentRow1046 := by rfl
theorem patch_mem6_3_1_0 : RadiusFivePruning.patch6_3_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1046, parentRow_mem1046, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1046_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_1_0]
  rfl
theorem row_eq6_3_1_3 : RadiusFivePruning.stateRow6_3_1_3 = ParentOwnership.parentRow1047 := by rfl
theorem patch_mem6_3_1_3 : RadiusFivePruning.patch6_3_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1047, parentRow_mem1047, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1047_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_1_3]
  rfl
theorem row_eq6_3_1_4 : RadiusFivePruning.stateRow6_3_1_4 = ParentOwnership.parentRow1053 := by rfl
theorem patch_mem6_3_1_4 : RadiusFivePruning.patch6_3_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1053, parentRow_mem1053, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1053_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_1_4]
  rfl
theorem row_eq6_3_1_5 : RadiusFivePruning.stateRow6_3_1_5 = ParentOwnership.parentRow1055 := by rfl
theorem patch_mem6_3_1_5 : RadiusFivePruning.patch6_3_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1055, parentRow_mem1055, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1055_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_1_5]
  rfl
theorem row_eq6_3_1_7 : RadiusFivePruning.stateRow6_3_1_7 = ParentOwnership.parentRow1061 := by rfl
theorem patch_mem6_3_1_7 : RadiusFivePruning.patch6_3_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1061, parentRow_mem1061, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1061_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_1_7]
  rfl
theorem row_eq6_3_1_8 : RadiusFivePruning.stateRow6_3_1_8 = ParentOwnership.parentRow1062 := by rfl
theorem patch_mem6_3_1_8 : RadiusFivePruning.patch6_3_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1062, parentRow_mem1062, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1062_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_1_8]
  rfl
theorem row_eq6_3_1_10 : RadiusFivePruning.stateRow6_3_1_10 = ParentOwnership.parentRow1064 := by rfl
theorem patch_mem6_3_1_10 : RadiusFivePruning.patch6_3_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1064, parentRow_mem1064, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1064_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_1_10]
  rfl
theorem row_eq6_3_1_11 : RadiusFivePruning.stateRow6_3_1_11 = ParentOwnership.parentRow1259 := by rfl
theorem patch_mem6_3_1_11 : RadiusFivePruning.patch6_3_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1259, parentRow_mem1259, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1259_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_1_11]
  rfl
theorem chunk_mem6_3_1 : ∀ p ∈ RadiusFivePruning.final6_3_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_3_1, List.forall_mem_cons]
  exact ⟨patch_mem6_3_1_0,⟨patch_mem6_3_1_3,⟨patch_mem6_3_1_4,⟨patch_mem6_3_1_5,⟨patch_mem6_3_1_7,⟨patch_mem6_3_1_8,⟨patch_mem6_3_1_10,⟨patch_mem6_3_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_3_2_0 : RadiusFivePruning.stateRow6_3_2_0 = ParentOwnership.parentRow1048 := by rfl
theorem patch_mem6_3_2_0 : RadiusFivePruning.patch6_3_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1048, parentRow_mem1048, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1048_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_2_0]
  rfl
theorem row_eq6_3_2_1 : RadiusFivePruning.stateRow6_3_2_1 = ParentOwnership.parentRow1056 := by rfl
theorem patch_mem6_3_2_1 : RadiusFivePruning.patch6_3_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1056, parentRow_mem1056, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1056_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_2_1]
  rfl
theorem row_eq6_3_2_2 : RadiusFivePruning.stateRow6_3_2_2 = ParentOwnership.parentRow0079 := by rfl
theorem patch_mem6_3_2_2 : RadiusFivePruning.patch6_3_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0079, parentRow_mem0079, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0079_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_2_2]
  rfl
theorem row_eq6_3_2_5 : RadiusFivePruning.stateRow6_3_2_5 = ParentOwnership.parentRow1252 := by rfl
theorem patch_mem6_3_2_5 : RadiusFivePruning.patch6_3_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1252, parentRow_mem1252, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1252_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_2_5]
  rfl
theorem row_eq6_3_2_6 : RadiusFivePruning.stateRow6_3_2_6 = ParentOwnership.parentRow1045 := by rfl
theorem patch_mem6_3_2_6 : RadiusFivePruning.patch6_3_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1045, parentRow_mem1045, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1045_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_2_6]
  rfl
theorem row_eq6_3_2_7 : RadiusFivePruning.stateRow6_3_2_7 = ParentOwnership.parentRow1052 := by rfl
theorem patch_mem6_3_2_7 : RadiusFivePruning.patch6_3_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1052, parentRow_mem1052, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1052_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_2_7]
  rfl
theorem row_eq6_3_2_8 : RadiusFivePruning.stateRow6_3_2_8 = ParentOwnership.parentRow1054 := by rfl
theorem patch_mem6_3_2_8 : RadiusFivePruning.patch6_3_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1054, parentRow_mem1054, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1054_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_2_8]
  rfl
theorem row_eq6_3_2_9 : RadiusFivePruning.stateRow6_3_2_9 = ParentOwnership.parentRow0075 := by rfl
theorem patch_mem6_3_2_9 : RadiusFivePruning.patch6_3_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0075, parentRow_mem0075, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0075_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_2_9]
  rfl
theorem row_eq6_3_2_10 : RadiusFivePruning.stateRow6_3_2_10 = ParentOwnership.parentRow1036 := by rfl
theorem patch_mem6_3_2_10 : RadiusFivePruning.patch6_3_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1036, parentRow_mem1036, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1036_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_2_10]
  rfl
theorem row_eq6_3_2_11 : RadiusFivePruning.stateRow6_3_2_11 = ParentOwnership.parentRow0078 := by rfl
theorem patch_mem6_3_2_11 : RadiusFivePruning.patch6_3_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0078, parentRow_mem0078, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0078_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_2_11]
  rfl
theorem chunk_mem6_3_2 : ∀ p ∈ RadiusFivePruning.final6_3_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_3_2, List.forall_mem_cons]
  exact ⟨patch_mem6_3_2_0,⟨patch_mem6_3_2_1,⟨patch_mem6_3_2_2,⟨patch_mem6_3_2_5,⟨patch_mem6_3_2_6,⟨patch_mem6_3_2_7,⟨patch_mem6_3_2_8,⟨patch_mem6_3_2_9,⟨patch_mem6_3_2_10,⟨patch_mem6_3_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_3_3_0 : RadiusFivePruning.stateRow6_3_3_0 = ParentOwnership.parentRow1039 := by rfl
theorem patch_mem6_3_3_0 : RadiusFivePruning.patch6_3_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1039, parentRow_mem1039, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1039_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_3_0]
  rfl
theorem row_eq6_3_3_1 : RadiusFivePruning.stateRow6_3_3_1 = ParentOwnership.parentRow0313 := by rfl
theorem patch_mem6_3_3_1 : RadiusFivePruning.patch6_3_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0313, parentRow_mem0313, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0313_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_3_1]
  rfl
theorem row_eq6_3_3_4 : RadiusFivePruning.stateRow6_3_3_4 = ParentOwnership.parentRow1068 := by rfl
theorem patch_mem6_3_3_4 : RadiusFivePruning.patch6_3_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1068, parentRow_mem1068, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1068_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_3_4]
  rfl
theorem row_eq6_3_3_5 : RadiusFivePruning.stateRow6_3_3_5 = ParentOwnership.parentRow0081 := by rfl
theorem patch_mem6_3_3_5 : RadiusFivePruning.patch6_3_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0081, parentRow_mem0081, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0081_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_3_5]
  rfl
theorem row_eq6_3_3_6 : RadiusFivePruning.stateRow6_3_3_6 = ParentOwnership.parentRow0314 := by rfl
theorem patch_mem6_3_3_6 : RadiusFivePruning.patch6_3_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0314, parentRow_mem0314, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0314_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_3_6]
  rfl
theorem row_eq6_3_3_7 : RadiusFivePruning.stateRow6_3_3_7 = ParentOwnership.parentRow1079 := by rfl
theorem patch_mem6_3_3_7 : RadiusFivePruning.patch6_3_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1079, parentRow_mem1079, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1079_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_3_7]
  rfl
theorem row_eq6_3_3_8 : RadiusFivePruning.stateRow6_3_3_8 = ParentOwnership.parentRow0312 := by rfl
theorem patch_mem6_3_3_8 : RadiusFivePruning.patch6_3_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0312, parentRow_mem0312, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0312_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_3_8]
  rfl
theorem row_eq6_3_3_9 : RadiusFivePruning.stateRow6_3_3_9 = ParentOwnership.parentRow1078 := by rfl
theorem patch_mem6_3_3_9 : RadiusFivePruning.patch6_3_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1078, parentRow_mem1078, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1078_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_3_9]
  rfl
theorem row_eq6_3_3_10 : RadiusFivePruning.stateRow6_3_3_10 = ParentOwnership.parentRow0082 := by rfl
theorem patch_mem6_3_3_10 : RadiusFivePruning.patch6_3_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0082, parentRow_mem0082, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0082_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_3_10]
  rfl
theorem row_eq6_3_3_11 : RadiusFivePruning.stateRow6_3_3_11 = ParentOwnership.parentRow1069 := by rfl
theorem patch_mem6_3_3_11 : RadiusFivePruning.patch6_3_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1069, parentRow_mem1069, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1069_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_3_3_11]
  rfl
theorem chunk_mem6_3_3 : ∀ p ∈ RadiusFivePruning.final6_3_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_3_3, List.forall_mem_cons]
  exact ⟨patch_mem6_3_3_0,⟨patch_mem6_3_3_1,⟨patch_mem6_3_3_4,⟨patch_mem6_3_3_5,⟨patch_mem6_3_3_6,⟨patch_mem6_3_3_7,⟨patch_mem6_3_3_8,⟨patch_mem6_3_3_9,⟨patch_mem6_3_3_10,⟨patch_mem6_3_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
