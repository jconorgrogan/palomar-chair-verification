module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock0T4C4
public import SpectreFinite.RadiusFivePruningLiteralBlock0T5C0
public import SpectreFinite.RadiusFivePruningLiteralBlock0T5C1
public import SpectreFinite.RadiusFivePruningLiteralBlock0T5C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq0_4_4_0 : RadiusFivePruning.stateRow0_4_4_0 = ParentOwnership.parentRow0283 := by rfl
theorem patch_mem0_4_4_0 : RadiusFivePruning.patch0_4_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0283, parentRow_mem0283, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0283_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_4_4_0]
  rfl
theorem row_eq0_4_4_1 : RadiusFivePruning.stateRow0_4_4_1 = ParentOwnership.parentRow0586 := by rfl
theorem patch_mem0_4_4_1 : RadiusFivePruning.patch0_4_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0586, parentRow_mem0586, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0586_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_4_4_1]
  rfl
theorem row_eq0_4_4_2 : RadiusFivePruning.stateRow0_4_4_2 = ParentOwnership.parentRow0588 := by rfl
theorem patch_mem0_4_4_2 : RadiusFivePruning.patch0_4_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0588, parentRow_mem0588, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0588_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_4_4_2]
  rfl
theorem row_eq0_4_4_4 : RadiusFivePruning.stateRow0_4_4_4 = ParentOwnership.parentRow1302 := by rfl
theorem patch_mem0_4_4_4 : RadiusFivePruning.patch0_4_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1302, parentRow_mem1302, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1302_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_4_4_4]
  rfl
theorem row_eq0_4_4_6 : RadiusFivePruning.stateRow0_4_4_6 = ParentOwnership.parentRow0133 := by rfl
theorem patch_mem0_4_4_6 : RadiusFivePruning.patch0_4_4_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0133, parentRow_mem0133, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0133_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_4_4_6]
  rfl
theorem row_eq0_4_4_7 : RadiusFivePruning.stateRow0_4_4_7 = ParentOwnership.parentRow0277 := by rfl
theorem patch_mem0_4_4_7 : RadiusFivePruning.patch0_4_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0277, parentRow_mem0277, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0277_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_4_4_7]
  rfl
theorem row_eq0_4_4_8 : RadiusFivePruning.stateRow0_4_4_8 = ParentOwnership.parentRow0824 := by rfl
theorem patch_mem0_4_4_8 : RadiusFivePruning.patch0_4_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0824, parentRow_mem0824, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0824_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_4_4_8]
  rfl
theorem row_eq0_4_4_9 : RadiusFivePruning.stateRow0_4_4_9 = ParentOwnership.parentRow0825 := by rfl
theorem patch_mem0_4_4_9 : RadiusFivePruning.patch0_4_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0825, parentRow_mem0825, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0825_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_4_4_9]
  rfl
theorem row_eq0_4_4_10 : RadiusFivePruning.stateRow0_4_4_10 = ParentOwnership.parentRow0584 := by rfl
theorem patch_mem0_4_4_10 : RadiusFivePruning.patch0_4_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0584, parentRow_mem0584, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0584_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_4_4_10]
  rfl
theorem chunk_mem0_4_4 : ∀ p ∈ RadiusFivePruning.final0_4_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_4_4, List.forall_mem_cons]
  exact ⟨patch_mem0_4_4_0,⟨patch_mem0_4_4_1,⟨patch_mem0_4_4_2,⟨patch_mem0_4_4_4,⟨patch_mem0_4_4_6,⟨patch_mem0_4_4_7,⟨patch_mem0_4_4_8,⟨patch_mem0_4_4_9,⟨patch_mem0_4_4_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_5_0_0 : RadiusFivePruning.stateRow0_5_0_0 = ParentOwnership.parentRow1093 := by rfl
theorem patch_mem0_5_0_0 : RadiusFivePruning.patch0_5_0_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1093, parentRow_mem1093, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1093_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_0_0]
  rfl
theorem row_eq0_5_0_1 : RadiusFivePruning.stateRow0_5_0_1 = ParentOwnership.parentRow0197 := by rfl
theorem patch_mem0_5_0_1 : RadiusFivePruning.patch0_5_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0197, parentRow_mem0197, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0197_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_0_1]
  rfl
theorem row_eq0_5_0_3 : RadiusFivePruning.stateRow0_5_0_3 = ParentOwnership.parentRow1094 := by rfl
theorem patch_mem0_5_0_3 : RadiusFivePruning.patch0_5_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1094, parentRow_mem1094, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1094_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_0_3]
  rfl
theorem row_eq0_5_0_4 : RadiusFivePruning.stateRow0_5_0_4 = ParentOwnership.parentRow1095 := by rfl
theorem patch_mem0_5_0_4 : RadiusFivePruning.patch0_5_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1095, parentRow_mem1095, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1095_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_0_4]
  rfl
theorem row_eq0_5_0_5 : RadiusFivePruning.stateRow0_5_0_5 = ParentOwnership.parentRow1096 := by rfl
theorem patch_mem0_5_0_5 : RadiusFivePruning.patch0_5_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1096, parentRow_mem1096, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1096_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_0_5]
  rfl
theorem row_eq0_5_0_6 : RadiusFivePruning.stateRow0_5_0_6 = ParentOwnership.parentRow1099 := by rfl
theorem patch_mem0_5_0_6 : RadiusFivePruning.patch0_5_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1099, parentRow_mem1099, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1099_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_0_6]
  rfl
theorem row_eq0_5_0_8 : RadiusFivePruning.stateRow0_5_0_8 = ParentOwnership.parentRow0143 := by rfl
theorem patch_mem0_5_0_8 : RadiusFivePruning.patch0_5_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0143, parentRow_mem0143, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0143_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_0_8]
  rfl
theorem row_eq0_5_0_9 : RadiusFivePruning.stateRow0_5_0_9 = ParentOwnership.parentRow1100 := by rfl
theorem patch_mem0_5_0_9 : RadiusFivePruning.patch0_5_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1100, parentRow_mem1100, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1100_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_0_9]
  rfl
theorem row_eq0_5_0_10 : RadiusFivePruning.stateRow0_5_0_10 = ParentOwnership.parentRow1101 := by rfl
theorem patch_mem0_5_0_10 : RadiusFivePruning.patch0_5_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1101, parentRow_mem1101, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1101_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_0_10]
  rfl
theorem row_eq0_5_0_11 : RadiusFivePruning.stateRow0_5_0_11 = ParentOwnership.parentRow1102 := by rfl
theorem patch_mem0_5_0_11 : RadiusFivePruning.patch0_5_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1102, parentRow_mem1102, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1102_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_0_11]
  rfl
theorem chunk_mem0_5_0 : ∀ p ∈ RadiusFivePruning.final0_5_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_5_0, List.forall_mem_cons]
  exact ⟨patch_mem0_5_0_0,⟨patch_mem0_5_0_1,⟨patch_mem0_5_0_3,⟨patch_mem0_5_0_4,⟨patch_mem0_5_0_5,⟨patch_mem0_5_0_6,⟨patch_mem0_5_0_8,⟨patch_mem0_5_0_9,⟨patch_mem0_5_0_10,⟨patch_mem0_5_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_5_1_0 : RadiusFivePruning.stateRow0_5_1_0 = ParentOwnership.parentRow1103 := by rfl
theorem patch_mem0_5_1_0 : RadiusFivePruning.patch0_5_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1103, parentRow_mem1103, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1103_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_1_0]
  rfl
theorem row_eq0_5_1_2 : RadiusFivePruning.stateRow0_5_1_2 = ParentOwnership.parentRow1067 := by rfl
theorem patch_mem0_5_1_2 : RadiusFivePruning.patch0_5_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1067, parentRow_mem1067, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1067_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_1_2]
  rfl
theorem row_eq0_5_1_4 : RadiusFivePruning.stateRow0_5_1_4 = ParentOwnership.parentRow1059 := by rfl
theorem patch_mem0_5_1_4 : RadiusFivePruning.patch0_5_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1059, parentRow_mem1059, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1059_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_1_4]
  rfl
theorem row_eq0_5_1_5 : RadiusFivePruning.stateRow0_5_1_5 = ParentOwnership.parentRow0311 := by rfl
theorem patch_mem0_5_1_5 : RadiusFivePruning.patch0_5_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0311, parentRow_mem0311, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0311_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_1_5]
  rfl
theorem row_eq0_5_1_6 : RadiusFivePruning.stateRow0_5_1_6 = ParentOwnership.parentRow0310 := by rfl
theorem patch_mem0_5_1_6 : RadiusFivePruning.patch0_5_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0310, parentRow_mem0310, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0310_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_1_6]
  rfl
theorem row_eq0_5_1_9 : RadiusFivePruning.stateRow0_5_1_9 = ParentOwnership.parentRow1076 := by rfl
theorem patch_mem0_5_1_9 : RadiusFivePruning.patch0_5_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1076, parentRow_mem1076, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1076_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_1_9]
  rfl
theorem row_eq0_5_1_11 : RadiusFivePruning.stateRow0_5_1_11 = ParentOwnership.parentRow1077 := by rfl
theorem patch_mem0_5_1_11 : RadiusFivePruning.patch0_5_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1077, parentRow_mem1077, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1077_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_1_11]
  rfl
theorem chunk_mem0_5_1 : ∀ p ∈ RadiusFivePruning.final0_5_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_5_1, List.forall_mem_cons]
  exact ⟨patch_mem0_5_1_0,⟨patch_mem0_5_1_2,⟨patch_mem0_5_1_4,⟨patch_mem0_5_1_5,⟨patch_mem0_5_1_6,⟨patch_mem0_5_1_9,⟨patch_mem0_5_1_11,by simp⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_5_2_0 : RadiusFivePruning.stateRow0_5_2_0 = ParentOwnership.parentRow1044 := by rfl
theorem patch_mem0_5_2_0 : RadiusFivePruning.patch0_5_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1044, parentRow_mem1044, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1044_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_2_0]
  rfl
theorem row_eq0_5_2_1 : RadiusFivePruning.stateRow0_5_2_1 = ParentOwnership.parentRow0155 := by rfl
theorem patch_mem0_5_2_1 : RadiusFivePruning.patch0_5_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0155, parentRow_mem0155, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0155_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_2_1]
  rfl
theorem row_eq0_5_2_2 : RadiusFivePruning.stateRow0_5_2_2 = ParentOwnership.parentRow0156 := by rfl
theorem patch_mem0_5_2_2 : RadiusFivePruning.patch0_5_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0156, parentRow_mem0156, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0156_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_2_2]
  rfl
theorem row_eq0_5_2_3 : RadiusFivePruning.stateRow0_5_2_3 = ParentOwnership.parentRow0154 := by rfl
theorem patch_mem0_5_2_3 : RadiusFivePruning.patch0_5_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0154, parentRow_mem0154, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0154_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_2_3]
  rfl
theorem row_eq0_5_2_5 : RadiusFivePruning.stateRow0_5_2_5 = ParentOwnership.parentRow1042 := by rfl
theorem patch_mem0_5_2_5 : RadiusFivePruning.patch0_5_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1042, parentRow_mem1042, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1042_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_2_5]
  rfl
theorem row_eq0_5_2_6 : RadiusFivePruning.stateRow0_5_2_6 = ParentOwnership.parentRow1043 := by rfl
theorem patch_mem0_5_2_6 : RadiusFivePruning.patch0_5_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1043, parentRow_mem1043, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1043_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_2_6]
  rfl
theorem row_eq0_5_2_7 : RadiusFivePruning.stateRow0_5_2_7 = ParentOwnership.parentRow0152 := by rfl
theorem patch_mem0_5_2_7 : RadiusFivePruning.patch0_5_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0152, parentRow_mem0152, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0152_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_2_7]
  rfl
theorem row_eq0_5_2_8 : RadiusFivePruning.stateRow0_5_2_8 = ParentOwnership.parentRow0153 := by rfl
theorem patch_mem0_5_2_8 : RadiusFivePruning.patch0_5_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0153, parentRow_mem0153, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0153_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_2_8]
  rfl
theorem row_eq0_5_2_9 : RadiusFivePruning.stateRow0_5_2_9 = ParentOwnership.parentRow0150 := by rfl
theorem patch_mem0_5_2_9 : RadiusFivePruning.patch0_5_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0150, parentRow_mem0150, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0150_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_2_9]
  rfl
theorem row_eq0_5_2_10 : RadiusFivePruning.stateRow0_5_2_10 = ParentOwnership.parentRow0151 := by rfl
theorem patch_mem0_5_2_10 : RadiusFivePruning.patch0_5_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0151, parentRow_mem0151, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0151_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_2_10]
  rfl
theorem chunk_mem0_5_2 : ∀ p ∈ RadiusFivePruning.final0_5_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_5_2, List.forall_mem_cons]
  exact ⟨patch_mem0_5_2_0,⟨patch_mem0_5_2_1,⟨patch_mem0_5_2_2,⟨patch_mem0_5_2_3,⟨patch_mem0_5_2_5,⟨patch_mem0_5_2_6,⟨patch_mem0_5_2_7,⟨patch_mem0_5_2_8,⟨patch_mem0_5_2_9,⟨patch_mem0_5_2_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
