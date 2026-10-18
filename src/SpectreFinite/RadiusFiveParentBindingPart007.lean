module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock0T5C3
public import SpectreFinite.RadiusFivePruningLiteralBlock0T5C4
public import SpectreFinite.RadiusFivePruningLiteralBlock1T0C0
public import SpectreFinite.RadiusFivePruningLiteralBlock1T0C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq0_5_3_0 : RadiusFivePruning.stateRow0_5_3_0 = ParentOwnership.parentRow1051 := by rfl
theorem patch_mem0_5_3_0 : RadiusFivePruning.patch0_5_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1051, parentRow_mem1051, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1051_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_3_0]
  rfl
theorem row_eq0_5_3_2 : RadiusFivePruning.stateRow0_5_3_2 = ParentOwnership.parentRow0174 := by rfl
theorem patch_mem0_5_3_2 : RadiusFivePruning.patch0_5_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0174, parentRow_mem0174, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0174_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_3_2]
  rfl
theorem row_eq0_5_3_3 : RadiusFivePruning.stateRow0_5_3_3 = ParentOwnership.parentRow1114 := by rfl
theorem patch_mem0_5_3_3 : RadiusFivePruning.patch0_5_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1114, parentRow_mem1114, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1114_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_3_3]
  rfl
theorem row_eq0_5_3_4 : RadiusFivePruning.stateRow0_5_3_4 = ParentOwnership.parentRow1115 := by rfl
theorem patch_mem0_5_3_4 : RadiusFivePruning.patch0_5_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1115, parentRow_mem1115, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1115_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_3_4]
  rfl
theorem row_eq0_5_3_5 : RadiusFivePruning.stateRow0_5_3_5 = ParentOwnership.parentRow1116 := by rfl
theorem patch_mem0_5_3_5 : RadiusFivePruning.patch0_5_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1116, parentRow_mem1116, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1116_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_3_5]
  rfl
theorem row_eq0_5_3_6 : RadiusFivePruning.stateRow0_5_3_6 = ParentOwnership.parentRow0175 := by rfl
theorem patch_mem0_5_3_6 : RadiusFivePruning.patch0_5_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0175, parentRow_mem0175, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0175_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_3_6]
  rfl
theorem row_eq0_5_3_8 : RadiusFivePruning.stateRow0_5_3_8 = ParentOwnership.parentRow1058 := by rfl
theorem patch_mem0_5_3_8 : RadiusFivePruning.patch0_5_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1058, parentRow_mem1058, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1058_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_3_8]
  rfl
theorem row_eq0_5_3_9 : RadiusFivePruning.stateRow0_5_3_9 = ParentOwnership.parentRow0178 := by rfl
theorem patch_mem0_5_3_9 : RadiusFivePruning.patch0_5_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0178, parentRow_mem0178, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0178_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_3_9]
  rfl
theorem row_eq0_5_3_11 : RadiusFivePruning.stateRow0_5_3_11 = ParentOwnership.parentRow0176 := by rfl
theorem patch_mem0_5_3_11 : RadiusFivePruning.patch0_5_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0176, parentRow_mem0176, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0176_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_3_11]
  rfl
theorem chunk_mem0_5_3 : ∀ p ∈ RadiusFivePruning.final0_5_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_5_3, List.forall_mem_cons]
  exact ⟨patch_mem0_5_3_0,⟨patch_mem0_5_3_2,⟨patch_mem0_5_3_3,⟨patch_mem0_5_3_4,⟨patch_mem0_5_3_5,⟨patch_mem0_5_3_6,⟨patch_mem0_5_3_8,⟨patch_mem0_5_3_9,⟨patch_mem0_5_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_5_4_0 : RadiusFivePruning.stateRow0_5_4_0 = ParentOwnership.parentRow0177 := by rfl
theorem patch_mem0_5_4_0 : RadiusFivePruning.patch0_5_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0177, parentRow_mem0177, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0177_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_4_0]
  rfl
theorem row_eq0_5_4_1 : RadiusFivePruning.stateRow0_5_4_1 = ParentOwnership.parentRow1117 := by rfl
theorem patch_mem0_5_4_1 : RadiusFivePruning.patch0_5_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1117, parentRow_mem1117, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1117_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_4_1]
  rfl
theorem row_eq0_5_4_2 : RadiusFivePruning.stateRow0_5_4_2 = ParentOwnership.parentRow1118 := by rfl
theorem patch_mem0_5_4_2 : RadiusFivePruning.patch0_5_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1118, parentRow_mem1118, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1118_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_4_2]
  rfl
theorem row_eq0_5_4_4 : RadiusFivePruning.stateRow0_5_4_4 = ParentOwnership.parentRow0179 := by rfl
theorem patch_mem0_5_4_4 : RadiusFivePruning.patch0_5_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0179, parentRow_mem0179, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0179_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_4_4]
  rfl
theorem row_eq0_5_4_6 : RadiusFivePruning.stateRow0_5_4_6 = ParentOwnership.parentRow1040 := by rfl
theorem patch_mem0_5_4_6 : RadiusFivePruning.patch0_5_4_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1040, parentRow_mem1040, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1040_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_4_6]
  rfl
theorem row_eq0_5_4_7 : RadiusFivePruning.stateRow0_5_4_7 = ParentOwnership.parentRow0146 := by rfl
theorem patch_mem0_5_4_7 : RadiusFivePruning.patch0_5_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0146, parentRow_mem0146, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0146_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_4_7]
  rfl
theorem row_eq0_5_4_8 : RadiusFivePruning.stateRow0_5_4_8 = ParentOwnership.parentRow1105 := by rfl
theorem patch_mem0_5_4_8 : RadiusFivePruning.patch0_5_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1105, parentRow_mem1105, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1105_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_4_8]
  rfl
theorem row_eq0_5_4_9 : RadiusFivePruning.stateRow0_5_4_9 = ParentOwnership.parentRow1106 := by rfl
theorem patch_mem0_5_4_9 : RadiusFivePruning.patch0_5_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1106, parentRow_mem1106, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1106_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_4_9]
  rfl
theorem row_eq0_5_4_10 : RadiusFivePruning.stateRow0_5_4_10 = ParentOwnership.parentRow1107 := by rfl
theorem patch_mem0_5_4_10 : RadiusFivePruning.patch0_5_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1107, parentRow_mem1107, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1107_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_5_4_10]
  rfl
theorem chunk_mem0_5_4 : ∀ p ∈ RadiusFivePruning.final0_5_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_5_4, List.forall_mem_cons]
  exact ⟨patch_mem0_5_4_0,⟨patch_mem0_5_4_1,⟨patch_mem0_5_4_2,⟨patch_mem0_5_4_4,⟨patch_mem0_5_4_6,⟨patch_mem0_5_4_7,⟨patch_mem0_5_4_8,⟨patch_mem0_5_4_9,⟨patch_mem0_5_4_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_0_0_1 : RadiusFivePruning.stateRow1_0_0_1 = ParentOwnership.parentRow0704 := by rfl
theorem patch_mem1_0_0_1 : RadiusFivePruning.patch1_0_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0704, parentRow_mem0704, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0704_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_0_1]
  rfl
theorem row_eq1_0_0_2 : RadiusFivePruning.stateRow1_0_0_2 = ParentOwnership.parentRow0705 := by rfl
theorem patch_mem1_0_0_2 : RadiusFivePruning.patch1_0_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0705, parentRow_mem0705, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0705_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_0_2]
  rfl
theorem row_eq1_0_0_3 : RadiusFivePruning.stateRow1_0_0_3 = ParentOwnership.parentRow0706 := by rfl
theorem patch_mem1_0_0_3 : RadiusFivePruning.patch1_0_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0706, parentRow_mem0706, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0706_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_0_3]
  rfl
theorem row_eq1_0_0_5 : RadiusFivePruning.stateRow1_0_0_5 = ParentOwnership.parentRow0707 := by rfl
theorem patch_mem1_0_0_5 : RadiusFivePruning.patch1_0_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0707, parentRow_mem0707, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0707_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_0_5]
  rfl
theorem row_eq1_0_0_6 : RadiusFivePruning.stateRow1_0_0_6 = ParentOwnership.parentRow0708 := by rfl
theorem patch_mem1_0_0_6 : RadiusFivePruning.patch1_0_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0708, parentRow_mem0708, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0708_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_0_6]
  rfl
theorem row_eq1_0_0_7 : RadiusFivePruning.stateRow1_0_0_7 = ParentOwnership.parentRow0709 := by rfl
theorem patch_mem1_0_0_7 : RadiusFivePruning.patch1_0_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0709, parentRow_mem0709, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0709_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_0_7]
  rfl
theorem row_eq1_0_0_8 : RadiusFivePruning.stateRow1_0_0_8 = ParentOwnership.parentRow0710 := by rfl
theorem patch_mem1_0_0_8 : RadiusFivePruning.patch1_0_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0710, parentRow_mem0710, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0710_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_0_8]
  rfl
theorem row_eq1_0_0_9 : RadiusFivePruning.stateRow1_0_0_9 = ParentOwnership.parentRow0711 := by rfl
theorem patch_mem1_0_0_9 : RadiusFivePruning.patch1_0_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0711, parentRow_mem0711, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0711_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_0_9]
  rfl
theorem row_eq1_0_0_10 : RadiusFivePruning.stateRow1_0_0_10 = ParentOwnership.parentRow0719 := by rfl
theorem patch_mem1_0_0_10 : RadiusFivePruning.patch1_0_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0719, parentRow_mem0719, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0719_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_0_10]
  rfl
theorem row_eq1_0_0_11 : RadiusFivePruning.stateRow1_0_0_11 = ParentOwnership.parentRow0720 := by rfl
theorem patch_mem1_0_0_11 : RadiusFivePruning.patch1_0_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0720, parentRow_mem0720, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0720_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_0_11]
  rfl
theorem chunk_mem1_0_0 : ∀ p ∈ RadiusFivePruning.final1_0_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_0_0, List.forall_mem_cons]
  exact ⟨patch_mem1_0_0_1,⟨patch_mem1_0_0_2,⟨patch_mem1_0_0_3,⟨patch_mem1_0_0_5,⟨patch_mem1_0_0_6,⟨patch_mem1_0_0_7,⟨patch_mem1_0_0_8,⟨patch_mem1_0_0_9,⟨patch_mem1_0_0_10,⟨patch_mem1_0_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_0_1_1 : RadiusFivePruning.stateRow1_0_1_1 = ParentOwnership.parentRow0721 := by rfl
theorem patch_mem1_0_1_1 : RadiusFivePruning.patch1_0_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0721, parentRow_mem0721, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0721_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_1_1]
  rfl
theorem row_eq1_0_1_2 : RadiusFivePruning.stateRow1_0_1_2 = ParentOwnership.parentRow0722 := by rfl
theorem patch_mem1_0_1_2 : RadiusFivePruning.patch1_0_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0722, parentRow_mem0722, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0722_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_1_2]
  rfl
theorem row_eq1_0_1_3 : RadiusFivePruning.stateRow1_0_1_3 = ParentOwnership.parentRow0723 := by rfl
theorem patch_mem1_0_1_3 : RadiusFivePruning.patch1_0_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0723, parentRow_mem0723, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0723_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_1_3]
  rfl
theorem row_eq1_0_1_4 : RadiusFivePruning.stateRow1_0_1_4 = ParentOwnership.parentRow0724 := by rfl
theorem patch_mem1_0_1_4 : RadiusFivePruning.patch1_0_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0724, parentRow_mem0724, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0724_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_1_4]
  rfl
theorem row_eq1_0_1_5 : RadiusFivePruning.stateRow1_0_1_5 = ParentOwnership.parentRow1906 := by rfl
theorem patch_mem1_0_1_5 : RadiusFivePruning.patch1_0_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1906, parentRow_mem1906, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1906_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_1_5]
  rfl
theorem row_eq1_0_1_6 : RadiusFivePruning.stateRow1_0_1_6 = ParentOwnership.parentRow1907 := by rfl
theorem patch_mem1_0_1_6 : RadiusFivePruning.patch1_0_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1907, parentRow_mem1907, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1907_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_1_6]
  rfl
theorem row_eq1_0_1_8 : RadiusFivePruning.stateRow1_0_1_8 = ParentOwnership.parentRow1908 := by rfl
theorem patch_mem1_0_1_8 : RadiusFivePruning.patch1_0_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1908, parentRow_mem1908, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1908_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_1_8]
  rfl
theorem row_eq1_0_1_9 : RadiusFivePruning.stateRow1_0_1_9 = ParentOwnership.parentRow1909 := by rfl
theorem patch_mem1_0_1_9 : RadiusFivePruning.patch1_0_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1909, parentRow_mem1909, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1909_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_1_9]
  rfl
theorem row_eq1_0_1_10 : RadiusFivePruning.stateRow1_0_1_10 = ParentOwnership.parentRow1910 := by rfl
theorem patch_mem1_0_1_10 : RadiusFivePruning.patch1_0_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1910, parentRow_mem1910, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1910_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_1_10]
  rfl
theorem chunk_mem1_0_1 : ∀ p ∈ RadiusFivePruning.final1_0_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_0_1, List.forall_mem_cons]
  exact ⟨patch_mem1_0_1_1,⟨patch_mem1_0_1_2,⟨patch_mem1_0_1_3,⟨patch_mem1_0_1_4,⟨patch_mem1_0_1_5,⟨patch_mem1_0_1_6,⟨patch_mem1_0_1_8,⟨patch_mem1_0_1_9,⟨patch_mem1_0_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
