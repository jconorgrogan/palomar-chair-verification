module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock1T2C4
public import SpectreFinite.RadiusFivePruningLiteralBlock1T3C0
public import SpectreFinite.RadiusFivePruningLiteralBlock1T3C1
public import SpectreFinite.RadiusFivePruningLiteralBlock1T3C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq1_2_4_1 : RadiusFivePruning.stateRow1_2_4_1 = ParentOwnership.parentRow1112 := by rfl
theorem patch_mem1_2_4_1 : RadiusFivePruning.patch1_2_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1112, parentRow_mem1112, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1112_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_4_1]
  rfl
theorem row_eq1_2_4_2 : RadiusFivePruning.stateRow1_2_4_2 = ParentOwnership.parentRow1109 := by rfl
theorem patch_mem1_2_4_2 : RadiusFivePruning.patch1_2_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1109, parentRow_mem1109, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1109_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_4_2]
  rfl
theorem row_eq1_2_4_4 : RadiusFivePruning.stateRow1_2_4_4 = ParentOwnership.parentRow0219 := by rfl
theorem patch_mem1_2_4_4 : RadiusFivePruning.patch1_2_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0219, parentRow_mem0219, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0219_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_4_4]
  rfl
theorem row_eq1_2_4_7 : RadiusFivePruning.stateRow1_2_4_7 = ParentOwnership.parentRow0223 := by rfl
theorem patch_mem1_2_4_7 : RadiusFivePruning.patch1_2_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0223, parentRow_mem0223, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0223_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_4_7]
  rfl
theorem row_eq1_2_4_9 : RadiusFivePruning.stateRow1_2_4_9 = ParentOwnership.parentRow0222 := by rfl
theorem patch_mem1_2_4_9 : RadiusFivePruning.patch1_2_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0222, parentRow_mem0222, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0222_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_4_9]
  rfl
theorem row_eq1_2_4_10 : RadiusFivePruning.stateRow1_2_4_10 = ParentOwnership.parentRow0221 := by rfl
theorem patch_mem1_2_4_10 : RadiusFivePruning.patch1_2_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0221, parentRow_mem0221, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0221_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_2_4_10]
  rfl
theorem chunk_mem1_2_4 : ∀ p ∈ RadiusFivePruning.final1_2_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_2_4, List.forall_mem_cons]
  exact ⟨patch_mem1_2_4_1,⟨patch_mem1_2_4_2,⟨patch_mem1_2_4_4,⟨patch_mem1_2_4_7,⟨patch_mem1_2_4_9,⟨patch_mem1_2_4_10,by simp⟩⟩⟩⟩⟩⟩
theorem row_eq1_3_0_1 : RadiusFivePruning.stateRow1_3_0_1 = ParentOwnership.parentRow1258 := by rfl
theorem patch_mem1_3_0_1 : RadiusFivePruning.patch1_3_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1258, parentRow_mem1258, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1258_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_0_1]
  rfl
theorem row_eq1_3_0_2 : RadiusFivePruning.stateRow1_3_0_2 = ParentOwnership.parentRow0040 := by rfl
theorem patch_mem1_3_0_2 : RadiusFivePruning.patch1_3_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0040, parentRow_mem0040, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0040_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_0_2]
  rfl
theorem row_eq1_3_0_3 : RadiusFivePruning.stateRow1_3_0_3 = ParentOwnership.parentRow1251 := by rfl
theorem patch_mem1_3_0_3 : RadiusFivePruning.patch1_3_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1251, parentRow_mem1251, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1251_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_0_3]
  rfl
theorem row_eq1_3_0_5 : RadiusFivePruning.stateRow1_3_0_5 = ParentOwnership.parentRow1220 := by rfl
theorem patch_mem1_3_0_5 : RadiusFivePruning.patch1_3_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1220, parentRow_mem1220, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1220_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_0_5]
  rfl
theorem row_eq1_3_0_6 : RadiusFivePruning.stateRow1_3_0_6 = ParentOwnership.parentRow0073 := by rfl
theorem patch_mem1_3_0_6 : RadiusFivePruning.patch1_3_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0073, parentRow_mem0073, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0073_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_0_6]
  rfl
theorem row_eq1_3_0_7 : RadiusFivePruning.stateRow1_3_0_7 = ParentOwnership.parentRow1034 := by rfl
theorem patch_mem1_3_0_7 : RadiusFivePruning.patch1_3_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1034, parentRow_mem1034, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1034_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_0_7]
  rfl
theorem row_eq1_3_0_8 : RadiusFivePruning.stateRow1_3_0_8 = ParentOwnership.parentRow0074 := by rfl
theorem patch_mem1_3_0_8 : RadiusFivePruning.patch1_3_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0074, parentRow_mem0074, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0074_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_0_8]
  rfl
theorem row_eq1_3_0_9 : RadiusFivePruning.stateRow1_3_0_9 = ParentOwnership.parentRow1035 := by rfl
theorem patch_mem1_3_0_9 : RadiusFivePruning.patch1_3_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1035, parentRow_mem1035, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1035_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_0_9]
  rfl
theorem row_eq1_3_0_10 : RadiusFivePruning.stateRow1_3_0_10 = ParentOwnership.parentRow0044 := by rfl
theorem patch_mem1_3_0_10 : RadiusFivePruning.patch1_3_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0044, parentRow_mem0044, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0044_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_0_10]
  rfl
theorem row_eq1_3_0_11 : RadiusFivePruning.stateRow1_3_0_11 = ParentOwnership.parentRow1253 := by rfl
theorem patch_mem1_3_0_11 : RadiusFivePruning.patch1_3_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1253, parentRow_mem1253, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1253_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_0_11]
  rfl
theorem chunk_mem1_3_0 : ∀ p ∈ RadiusFivePruning.final1_3_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_3_0, List.forall_mem_cons]
  exact ⟨patch_mem1_3_0_1,⟨patch_mem1_3_0_2,⟨patch_mem1_3_0_3,⟨patch_mem1_3_0_5,⟨patch_mem1_3_0_6,⟨patch_mem1_3_0_7,⟨patch_mem1_3_0_8,⟨patch_mem1_3_0_9,⟨patch_mem1_3_0_10,⟨patch_mem1_3_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_3_1_1 : RadiusFivePruning.stateRow1_3_1_1 = ParentOwnership.parentRow0076 := by rfl
theorem patch_mem1_3_1_1 : RadiusFivePruning.patch1_3_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0076, parentRow_mem0076, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0076_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_1_1]
  rfl
theorem row_eq1_3_1_2 : RadiusFivePruning.stateRow1_3_1_2 = ParentOwnership.parentRow1037 := by rfl
theorem patch_mem1_3_1_2 : RadiusFivePruning.patch1_3_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1037, parentRow_mem1037, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1037_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_1_2]
  rfl
theorem row_eq1_3_1_3 : RadiusFivePruning.stateRow1_3_1_3 = ParentOwnership.parentRow0077 := by rfl
theorem patch_mem1_3_1_3 : RadiusFivePruning.patch1_3_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0077, parentRow_mem0077, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0077_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_1_3]
  rfl
theorem row_eq1_3_1_4 : RadiusFivePruning.stateRow1_3_1_4 = ParentOwnership.parentRow1038 := by rfl
theorem patch_mem1_3_1_4 : RadiusFivePruning.patch1_3_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1038, parentRow_mem1038, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1038_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_1_4]
  rfl
theorem row_eq1_3_1_5 : RadiusFivePruning.stateRow1_3_1_5 = ParentOwnership.parentRow1219 := by rfl
theorem patch_mem1_3_1_5 : RadiusFivePruning.patch1_3_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1219, parentRow_mem1219, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1219_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_1_5]
  rfl
theorem row_eq1_3_1_6 : RadiusFivePruning.stateRow1_3_1_6 = ParentOwnership.parentRow0141 := by rfl
theorem patch_mem1_3_1_6 : RadiusFivePruning.patch1_3_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0141, parentRow_mem0141, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0141_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_1_6]
  rfl
theorem row_eq1_3_1_8 : RadiusFivePruning.stateRow1_3_1_8 = ParentOwnership.parentRow0142 := by rfl
theorem patch_mem1_3_1_8 : RadiusFivePruning.patch1_3_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0142, parentRow_mem0142, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0142_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_1_8]
  rfl
theorem row_eq1_3_1_9 : RadiusFivePruning.stateRow1_3_1_9 = ParentOwnership.parentRow1098 := by rfl
theorem patch_mem1_3_1_9 : RadiusFivePruning.patch1_3_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1098, parentRow_mem1098, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1098_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_1_9]
  rfl
theorem row_eq1_3_1_10 : RadiusFivePruning.stateRow1_3_1_10 = ParentOwnership.parentRow0199 := by rfl
theorem patch_mem1_3_1_10 : RadiusFivePruning.patch1_3_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0199, parentRow_mem0199, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0199_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_1_10]
  rfl
theorem chunk_mem1_3_1 : ∀ p ∈ RadiusFivePruning.final1_3_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_3_1, List.forall_mem_cons]
  exact ⟨patch_mem1_3_1_1,⟨patch_mem1_3_1_2,⟨patch_mem1_3_1_3,⟨patch_mem1_3_1_4,⟨patch_mem1_3_1_5,⟨patch_mem1_3_1_6,⟨patch_mem1_3_1_8,⟨patch_mem1_3_1_9,⟨patch_mem1_3_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_3_2_0 : RadiusFivePruning.stateRow1_3_2_0 = ParentOwnership.parentRow0139 := by rfl
theorem patch_mem1_3_2_0 : RadiusFivePruning.patch1_3_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0139, parentRow_mem0139, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0139_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_2_0]
  rfl
theorem row_eq1_3_2_1 : RadiusFivePruning.stateRow1_3_2_1 = ParentOwnership.parentRow0200 := by rfl
theorem patch_mem1_3_2_1 : RadiusFivePruning.patch1_3_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0200, parentRow_mem0200, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0200_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_2_1]
  rfl
theorem row_eq1_3_2_2 : RadiusFivePruning.stateRow1_3_2_2 = ParentOwnership.parentRow0140 := by rfl
theorem patch_mem1_3_2_2 : RadiusFivePruning.patch1_3_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0140, parentRow_mem0140, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0140_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_2_2]
  rfl
theorem row_eq1_3_2_3 : RadiusFivePruning.stateRow1_3_2_3 = ParentOwnership.parentRow1097 := by rfl
theorem patch_mem1_3_2_3 : RadiusFivePruning.patch1_3_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1097, parentRow_mem1097, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1097_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_2_3]
  rfl
theorem row_eq1_3_2_4 : RadiusFivePruning.stateRow1_3_2_4 = ParentOwnership.parentRow0198 := by rfl
theorem patch_mem1_3_2_4 : RadiusFivePruning.patch1_3_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0198, parentRow_mem0198, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0198_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_2_4]
  rfl
theorem row_eq1_3_2_6 : RadiusFivePruning.stateRow1_3_2_6 = ParentOwnership.parentRow1261 := by rfl
theorem patch_mem1_3_2_6 : RadiusFivePruning.patch1_3_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1261, parentRow_mem1261, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1261_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_2_6]
  rfl
theorem row_eq1_3_2_7 : RadiusFivePruning.stateRow1_3_2_7 = ParentOwnership.parentRow1260 := by rfl
theorem patch_mem1_3_2_7 : RadiusFivePruning.patch1_3_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1260, parentRow_mem1260, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1260_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_2_7]
  rfl
theorem row_eq1_3_2_8 : RadiusFivePruning.stateRow1_3_2_8 = ParentOwnership.parentRow0046 := by rfl
theorem patch_mem1_3_2_8 : RadiusFivePruning.patch1_3_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0046, parentRow_mem0046, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0046_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_2_8]
  rfl
theorem row_eq1_3_2_9 : RadiusFivePruning.stateRow1_3_2_9 = ParentOwnership.parentRow1255 := by rfl
theorem patch_mem1_3_2_9 : RadiusFivePruning.patch1_3_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1255, parentRow_mem1255, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1255_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_2_9]
  rfl
theorem row_eq1_3_2_11 : RadiusFivePruning.stateRow1_3_2_11 = ParentOwnership.parentRow0045 := by rfl
theorem patch_mem1_3_2_11 : RadiusFivePruning.patch1_3_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0045, parentRow_mem0045, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0045_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_2_11]
  rfl
theorem chunk_mem1_3_2 : ∀ p ∈ RadiusFivePruning.final1_3_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_3_2, List.forall_mem_cons]
  exact ⟨patch_mem1_3_2_0,⟨patch_mem1_3_2_1,⟨patch_mem1_3_2_2,⟨patch_mem1_3_2_3,⟨patch_mem1_3_2_4,⟨patch_mem1_3_2_6,⟨patch_mem1_3_2_7,⟨patch_mem1_3_2_8,⟨patch_mem1_3_2_9,⟨patch_mem1_3_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
