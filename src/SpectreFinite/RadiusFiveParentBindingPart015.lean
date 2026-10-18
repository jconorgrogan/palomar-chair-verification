module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock2T0C0
public import SpectreFinite.RadiusFivePruningLiteralBlock2T1C0
public import SpectreFinite.RadiusFivePruningLiteralBlock2T2C0
public import SpectreFinite.RadiusFivePruningLiteralBlock2T3C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq2_0_0_1 : RadiusFivePruning.stateRow2_0_0_1 = ParentOwnership.parentRow0860 := by rfl
theorem patch_mem2_0_0_1 : RadiusFivePruning.patch2_0_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0860, parentRow_mem0860, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0860_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_0_0_1]
  rfl
theorem row_eq2_0_0_2 : RadiusFivePruning.stateRow2_0_0_2 = ParentOwnership.parentRow0861 := by rfl
theorem patch_mem2_0_0_2 : RadiusFivePruning.patch2_0_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0861, parentRow_mem0861, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0861_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_0_0_2]
  rfl
theorem row_eq2_0_0_3 : RadiusFivePruning.stateRow2_0_0_3 = ParentOwnership.parentRow0862 := by rfl
theorem patch_mem2_0_0_3 : RadiusFivePruning.patch2_0_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0862, parentRow_mem0862, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0862_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_0_0_3]
  rfl
theorem row_eq2_0_0_5 : RadiusFivePruning.stateRow2_0_0_5 = ParentOwnership.parentRow0960 := by rfl
theorem patch_mem2_0_0_5 : RadiusFivePruning.patch2_0_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0960, parentRow_mem0960, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0960_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_0_0_5]
  rfl
theorem chunk_mem2_0_0 : ∀ p ∈ RadiusFivePruning.final2_0_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final2_0_0, List.forall_mem_cons]
  exact ⟨patch_mem2_0_0_1,⟨patch_mem2_0_0_2,⟨patch_mem2_0_0_3,⟨patch_mem2_0_0_5,by simp⟩⟩⟩⟩
theorem row_eq2_1_0_1 : RadiusFivePruning.stateRow2_1_0_1 = ParentOwnership.parentRow1561 := by rfl
theorem patch_mem2_1_0_1 : RadiusFivePruning.patch2_1_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1561, parentRow_mem1561, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1561_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_1_0_1]
  rfl
theorem row_eq2_1_0_2 : RadiusFivePruning.stateRow2_1_0_2 = ParentOwnership.parentRow1599 := by rfl
theorem patch_mem2_1_0_2 : RadiusFivePruning.patch2_1_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1599, parentRow_mem1599, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1599_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_1_0_2]
  rfl
theorem row_eq2_1_0_3 : RadiusFivePruning.stateRow2_1_0_3 = ParentOwnership.parentRow1602 := by rfl
theorem patch_mem2_1_0_3 : RadiusFivePruning.patch2_1_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1602, parentRow_mem1602, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1602_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_1_0_3]
  rfl
theorem row_eq2_1_0_5 : RadiusFivePruning.stateRow2_1_0_5 = ParentOwnership.parentRow1558 := by rfl
theorem patch_mem2_1_0_5 : RadiusFivePruning.patch2_1_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1558, parentRow_mem1558, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1558_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_1_0_5]
  rfl
theorem chunk_mem2_1_0 : ∀ p ∈ RadiusFivePruning.final2_1_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final2_1_0, List.forall_mem_cons]
  exact ⟨patch_mem2_1_0_1,⟨patch_mem2_1_0_2,⟨patch_mem2_1_0_3,⟨patch_mem2_1_0_5,by simp⟩⟩⟩⟩
theorem row_eq2_2_0_1 : RadiusFivePruning.stateRow2_2_0_1 = ParentOwnership.parentRow0869 := by rfl
theorem patch_mem2_2_0_1 : RadiusFivePruning.patch2_2_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0869, parentRow_mem0869, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0869_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_2_0_1]
  rfl
theorem row_eq2_2_0_2 : RadiusFivePruning.stateRow2_2_0_2 = ParentOwnership.parentRow0966 := by rfl
theorem patch_mem2_2_0_2 : RadiusFivePruning.patch2_2_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0966, parentRow_mem0966, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0966_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_2_0_2]
  rfl
theorem row_eq2_2_0_3 : RadiusFivePruning.stateRow2_2_0_3 = ParentOwnership.parentRow0874 := by rfl
theorem patch_mem2_2_0_3 : RadiusFivePruning.patch2_2_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0874, parentRow_mem0874, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0874_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_2_0_3]
  rfl
theorem row_eq2_2_0_5 : RadiusFivePruning.stateRow2_2_0_5 = ParentOwnership.parentRow0868 := by rfl
theorem patch_mem2_2_0_5 : RadiusFivePruning.patch2_2_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0868, parentRow_mem0868, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0868_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_2_0_5]
  rfl
theorem chunk_mem2_2_0 : ∀ p ∈ RadiusFivePruning.final2_2_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final2_2_0, List.forall_mem_cons]
  exact ⟨patch_mem2_2_0_1,⟨patch_mem2_2_0_2,⟨patch_mem2_2_0_3,⟨patch_mem2_2_0_5,by simp⟩⟩⟩⟩
theorem row_eq2_3_0_1 : RadiusFivePruning.stateRow2_3_0_1 = ParentOwnership.parentRow0456 := by rfl
theorem patch_mem2_3_0_1 : RadiusFivePruning.patch2_3_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0456, parentRow_mem0456, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0456_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_3_0_1]
  rfl
theorem row_eq2_3_0_2 : RadiusFivePruning.stateRow2_3_0_2 = ParentOwnership.parentRow0428 := by rfl
theorem patch_mem2_3_0_2 : RadiusFivePruning.patch2_3_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0428, parentRow_mem0428, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0428_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_3_0_2]
  rfl
theorem row_eq2_3_0_3 : RadiusFivePruning.stateRow2_3_0_3 = ParentOwnership.parentRow0458 := by rfl
theorem patch_mem2_3_0_3 : RadiusFivePruning.patch2_3_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0458, parentRow_mem0458, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0458_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_3_0_3]
  rfl
theorem row_eq2_3_0_5 : RadiusFivePruning.stateRow2_3_0_5 = ParentOwnership.parentRow0457 := by rfl
theorem patch_mem2_3_0_5 : RadiusFivePruning.patch2_3_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0457, parentRow_mem0457, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0457_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_3_0_5]
  rfl
theorem chunk_mem2_3_0 : ∀ p ∈ RadiusFivePruning.final2_3_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final2_3_0, List.forall_mem_cons]
  exact ⟨patch_mem2_3_0_1,⟨patch_mem2_3_0_2,⟨patch_mem2_3_0_3,⟨patch_mem2_3_0_5,by simp⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
