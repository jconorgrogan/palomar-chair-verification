module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock2T4C0
public import SpectreFinite.RadiusFivePruningLiteralBlock2T5C0
public import SpectreFinite.RadiusFivePruningLiteralBlock3T0C0
public import SpectreFinite.RadiusFivePruningLiteralBlock3T1C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq2_4_0_1 : RadiusFivePruning.stateRow2_4_0_1 = ParentOwnership.parentRow0872 := by rfl
theorem patch_mem2_4_0_1 : RadiusFivePruning.patch2_4_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0872, parentRow_mem0872, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0872_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_4_0_1]
  rfl
theorem row_eq2_4_0_2 : RadiusFivePruning.stateRow2_4_0_2 = ParentOwnership.parentRow0867 := by rfl
theorem patch_mem2_4_0_2 : RadiusFivePruning.patch2_4_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0867, parentRow_mem0867, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0867_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_4_0_2]
  rfl
theorem row_eq2_4_0_3 : RadiusFivePruning.stateRow2_4_0_3 = ParentOwnership.parentRow0873 := by rfl
theorem patch_mem2_4_0_3 : RadiusFivePruning.patch2_4_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0873, parentRow_mem0873, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0873_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_4_0_3]
  rfl
theorem row_eq2_4_0_5 : RadiusFivePruning.stateRow2_4_0_5 = ParentOwnership.parentRow0871 := by rfl
theorem patch_mem2_4_0_5 : RadiusFivePruning.patch2_4_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0871, parentRow_mem0871, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0871_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_4_0_5]
  rfl
theorem chunk_mem2_4_0 : ∀ p ∈ RadiusFivePruning.final2_4_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final2_4_0, List.forall_mem_cons]
  exact ⟨patch_mem2_4_0_1,⟨patch_mem2_4_0_2,⟨patch_mem2_4_0_3,⟨patch_mem2_4_0_5,by simp⟩⟩⟩⟩
theorem row_eq2_5_0_1 : RadiusFivePruning.stateRow2_5_0_1 = ParentOwnership.parentRow0454 := by rfl
theorem patch_mem2_5_0_1 : RadiusFivePruning.patch2_5_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0454, parentRow_mem0454, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0454_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_5_0_1]
  rfl
theorem row_eq2_5_0_2 : RadiusFivePruning.stateRow2_5_0_2 = ParentOwnership.parentRow0453 := by rfl
theorem patch_mem2_5_0_2 : RadiusFivePruning.patch2_5_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0453, parentRow_mem0453, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0453_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_5_0_2]
  rfl
theorem row_eq2_5_0_3 : RadiusFivePruning.stateRow2_5_0_3 = ParentOwnership.parentRow0455 := by rfl
theorem patch_mem2_5_0_3 : RadiusFivePruning.patch2_5_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0455, parentRow_mem0455, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0455_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_5_0_3]
  rfl
theorem row_eq2_5_0_5 : RadiusFivePruning.stateRow2_5_0_5 = ParentOwnership.parentRow0440 := by rfl
theorem patch_mem2_5_0_5 : RadiusFivePruning.patch2_5_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0440, parentRow_mem0440, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0440_property.1, ← literalDomain_eq_hexRegion, ← row_eq2_5_0_5]
  rfl
theorem chunk_mem2_5_0 : ∀ p ∈ RadiusFivePruning.final2_5_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final2_5_0, List.forall_mem_cons]
  exact ⟨patch_mem2_5_0_1,⟨patch_mem2_5_0_2,⟨patch_mem2_5_0_3,⟨patch_mem2_5_0_5,by simp⟩⟩⟩⟩
theorem row_eq3_0_0_1 : RadiusFivePruning.stateRow3_0_0_1 = ParentOwnership.parentRow1626 := by rfl
theorem patch_mem3_0_0_1 : RadiusFivePruning.patch3_0_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1626, parentRow_mem1626, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1626_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_0_0_1]
  rfl
theorem row_eq3_0_0_3 : RadiusFivePruning.stateRow3_0_0_3 = ParentOwnership.parentRow1627 := by rfl
theorem patch_mem3_0_0_3 : RadiusFivePruning.patch3_0_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1627, parentRow_mem1627, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1627_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_0_0_3]
  rfl
theorem row_eq3_0_0_4 : RadiusFivePruning.stateRow3_0_0_4 = ParentOwnership.parentRow1628 := by rfl
theorem patch_mem3_0_0_4 : RadiusFivePruning.patch3_0_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1628, parentRow_mem1628, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1628_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_0_0_4]
  rfl
theorem row_eq3_0_0_5 : RadiusFivePruning.stateRow3_0_0_5 = ParentOwnership.parentRow1632 := by rfl
theorem patch_mem3_0_0_5 : RadiusFivePruning.patch3_0_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1632, parentRow_mem1632, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1632_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_0_0_5]
  rfl
theorem row_eq3_0_0_6 : RadiusFivePruning.stateRow3_0_0_6 = ParentOwnership.parentRow1633 := by rfl
theorem patch_mem3_0_0_6 : RadiusFivePruning.patch3_0_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1633, parentRow_mem1633, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1633_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_0_0_6]
  rfl
theorem chunk_mem3_0_0 : ∀ p ∈ RadiusFivePruning.final3_0_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final3_0_0, List.forall_mem_cons]
  exact ⟨patch_mem3_0_0_1,⟨patch_mem3_0_0_3,⟨patch_mem3_0_0_4,⟨patch_mem3_0_0_5,⟨patch_mem3_0_0_6,by simp⟩⟩⟩⟩⟩
theorem row_eq3_1_0_1 : RadiusFivePruning.stateRow3_1_0_1 = ParentOwnership.parentRow0752 := by rfl
theorem patch_mem3_1_0_1 : RadiusFivePruning.patch3_1_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0752, parentRow_mem0752, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0752_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_1_0_1]
  rfl
theorem row_eq3_1_0_3 : RadiusFivePruning.stateRow3_1_0_3 = ParentOwnership.parentRow1977 := by rfl
theorem patch_mem3_1_0_3 : RadiusFivePruning.patch3_1_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1977, parentRow_mem1977, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1977_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_1_0_3]
  rfl
theorem row_eq3_1_0_4 : RadiusFivePruning.stateRow3_1_0_4 = ParentOwnership.parentRow1978 := by rfl
theorem patch_mem3_1_0_4 : RadiusFivePruning.patch3_1_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1978, parentRow_mem1978, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1978_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_1_0_4]
  rfl
theorem row_eq3_1_0_5 : RadiusFivePruning.stateRow3_1_0_5 = ParentOwnership.parentRow1979 := by rfl
theorem patch_mem3_1_0_5 : RadiusFivePruning.patch3_1_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1979, parentRow_mem1979, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1979_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_1_0_5]
  rfl
theorem row_eq3_1_0_6 : RadiusFivePruning.stateRow3_1_0_6 = ParentOwnership.parentRow1980 := by rfl
theorem patch_mem3_1_0_6 : RadiusFivePruning.patch3_1_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1980, parentRow_mem1980, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1980_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_1_0_6]
  rfl
theorem chunk_mem3_1_0 : ∀ p ∈ RadiusFivePruning.final3_1_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final3_1_0, List.forall_mem_cons]
  exact ⟨patch_mem3_1_0_1,⟨patch_mem3_1_0_3,⟨patch_mem3_1_0_4,⟨patch_mem3_1_0_5,⟨patch_mem3_1_0_6,by simp⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
