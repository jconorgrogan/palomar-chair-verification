module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock6T5C0
public import SpectreFinite.RadiusFivePruningLiteralBlock6T5C1
public import SpectreFinite.RadiusFivePruningLiteralBlock6T5C2
public import SpectreFinite.RadiusFivePruningLiteralBlock6T5C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq6_5_0_2 : RadiusFivePruning.stateRow6_5_0_2 = ParentOwnership.parentRow2060 := by rfl
theorem patch_mem6_5_0_2 : RadiusFivePruning.patch6_5_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2060, parentRow_mem2060, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2060_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_0_2]
  rfl
theorem row_eq6_5_0_3 : RadiusFivePruning.stateRow6_5_0_3 = ParentOwnership.parentRow2062 := by rfl
theorem patch_mem6_5_0_3 : RadiusFivePruning.patch6_5_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2062, parentRow_mem2062, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2062_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_0_3]
  rfl
theorem row_eq6_5_0_5 : RadiusFivePruning.stateRow6_5_0_5 = ParentOwnership.parentRow2063 := by rfl
theorem patch_mem6_5_0_5 : RadiusFivePruning.patch6_5_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2063, parentRow_mem2063, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2063_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_0_5]
  rfl
theorem row_eq6_5_0_6 : RadiusFivePruning.stateRow6_5_0_6 = ParentOwnership.parentRow2061 := by rfl
theorem patch_mem6_5_0_6 : RadiusFivePruning.patch6_5_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2061, parentRow_mem2061, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2061_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_0_6]
  rfl
theorem row_eq6_5_0_8 : RadiusFivePruning.stateRow6_5_0_8 = ParentOwnership.parentRow0614 := by rfl
theorem patch_mem6_5_0_8 : RadiusFivePruning.patch6_5_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0614, parentRow_mem0614, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0614_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_0_8]
  rfl
theorem row_eq6_5_0_10 : RadiusFivePruning.stateRow6_5_0_10 = ParentOwnership.parentRow0615 := by rfl
theorem patch_mem6_5_0_10 : RadiusFivePruning.patch6_5_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0615, parentRow_mem0615, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0615_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_0_10]
  rfl
theorem chunk_mem6_5_0 : ∀ p ∈ RadiusFivePruning.final6_5_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_5_0, List.forall_mem_cons]
  exact ⟨patch_mem6_5_0_2,⟨patch_mem6_5_0_3,⟨patch_mem6_5_0_5,⟨patch_mem6_5_0_6,⟨patch_mem6_5_0_8,⟨patch_mem6_5_0_10,by simp⟩⟩⟩⟩⟩⟩
theorem row_eq6_5_1_0 : RadiusFivePruning.stateRow6_5_1_0 = ParentOwnership.parentRow0616 := by rfl
theorem patch_mem6_5_1_0 : RadiusFivePruning.patch6_5_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0616, parentRow_mem0616, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0616_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_1_0]
  rfl
theorem row_eq6_5_1_3 : RadiusFivePruning.stateRow6_5_1_3 = ParentOwnership.parentRow0617 := by rfl
theorem patch_mem6_5_1_3 : RadiusFivePruning.patch6_5_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0617, parentRow_mem0617, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0617_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_1_3]
  rfl
theorem row_eq6_5_1_4 : RadiusFivePruning.stateRow6_5_1_4 = ParentOwnership.parentRow0618 := by rfl
theorem patch_mem6_5_1_4 : RadiusFivePruning.patch6_5_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0618, parentRow_mem0618, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0618_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_1_4]
  rfl
theorem row_eq6_5_1_5 : RadiusFivePruning.stateRow6_5_1_5 = ParentOwnership.parentRow0619 := by rfl
theorem patch_mem6_5_1_5 : RadiusFivePruning.patch6_5_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0619, parentRow_mem0619, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0619_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_1_5]
  rfl
theorem row_eq6_5_1_7 : RadiusFivePruning.stateRow6_5_1_7 = ParentOwnership.parentRow0613 := by rfl
theorem patch_mem6_5_1_7 : RadiusFivePruning.patch6_5_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0613, parentRow_mem0613, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0613_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_1_7]
  rfl
theorem row_eq6_5_1_8 : RadiusFivePruning.stateRow6_5_1_8 = ParentOwnership.parentRow0993 := by rfl
theorem patch_mem6_5_1_8 : RadiusFivePruning.patch6_5_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0993, parentRow_mem0993, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0993_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_1_8]
  rfl
theorem row_eq6_5_1_10 : RadiusFivePruning.stateRow6_5_1_10 = ParentOwnership.parentRow0994 := by rfl
theorem patch_mem6_5_1_10 : RadiusFivePruning.patch6_5_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0994, parentRow_mem0994, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0994_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_1_10]
  rfl
theorem row_eq6_5_1_11 : RadiusFivePruning.stateRow6_5_1_11 = ParentOwnership.parentRow1005 := by rfl
theorem patch_mem6_5_1_11 : RadiusFivePruning.patch6_5_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1005, parentRow_mem1005, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1005_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_1_11]
  rfl
theorem chunk_mem6_5_1 : ∀ p ∈ RadiusFivePruning.final6_5_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_5_1, List.forall_mem_cons]
  exact ⟨patch_mem6_5_1_0,⟨patch_mem6_5_1_3,⟨patch_mem6_5_1_4,⟨patch_mem6_5_1_5,⟨patch_mem6_5_1_7,⟨patch_mem6_5_1_8,⟨patch_mem6_5_1_10,⟨patch_mem6_5_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_5_2_0 : RadiusFivePruning.stateRow6_5_2_0 = ParentOwnership.parentRow0995 := by rfl
theorem patch_mem6_5_2_0 : RadiusFivePruning.patch6_5_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0995, parentRow_mem0995, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0995_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_2_0]
  rfl
theorem row_eq6_5_2_1 : RadiusFivePruning.stateRow6_5_2_1 = ParentOwnership.parentRow0997 := by rfl
theorem patch_mem6_5_2_1 : RadiusFivePruning.patch6_5_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0997, parentRow_mem0997, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0997_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_2_1]
  rfl
theorem row_eq6_5_2_2 : RadiusFivePruning.stateRow6_5_2_2 = ParentOwnership.parentRow1008 := by rfl
theorem patch_mem6_5_2_2 : RadiusFivePruning.patch6_5_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1008, parentRow_mem1008, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1008_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_2_2]
  rfl
theorem row_eq6_5_2_5 : RadiusFivePruning.stateRow6_5_2_5 = ParentOwnership.parentRow1007 := by rfl
theorem patch_mem6_5_2_5 : RadiusFivePruning.patch6_5_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1007, parentRow_mem1007, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1007_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_2_5]
  rfl
theorem row_eq6_5_2_6 : RadiusFivePruning.stateRow6_5_2_6 = ParentOwnership.parentRow0996 := by rfl
theorem patch_mem6_5_2_6 : RadiusFivePruning.patch6_5_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0996, parentRow_mem0996, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0996_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_2_6]
  rfl
theorem row_eq6_5_2_7 : RadiusFivePruning.stateRow6_5_2_7 = ParentOwnership.parentRow0998 := by rfl
theorem patch_mem6_5_2_7 : RadiusFivePruning.patch6_5_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0998, parentRow_mem0998, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0998_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_2_7]
  rfl
theorem row_eq6_5_2_8 : RadiusFivePruning.stateRow6_5_2_8 = ParentOwnership.parentRow0999 := by rfl
theorem patch_mem6_5_2_8 : RadiusFivePruning.patch6_5_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0999, parentRow_mem0999, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0999_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_2_8]
  rfl
theorem row_eq6_5_2_9 : RadiusFivePruning.stateRow6_5_2_9 = ParentOwnership.parentRow1009 := by rfl
theorem patch_mem6_5_2_9 : RadiusFivePruning.patch6_5_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1009, parentRow_mem1009, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1009_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_2_9]
  rfl
theorem row_eq6_5_2_10 : RadiusFivePruning.stateRow6_5_2_10 = ParentOwnership.parentRow1010 := by rfl
theorem patch_mem6_5_2_10 : RadiusFivePruning.patch6_5_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1010, parentRow_mem1010, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1010_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_2_10]
  rfl
theorem row_eq6_5_2_11 : RadiusFivePruning.stateRow6_5_2_11 = ParentOwnership.parentRow1011 := by rfl
theorem patch_mem6_5_2_11 : RadiusFivePruning.patch6_5_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1011, parentRow_mem1011, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1011_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_2_11]
  rfl
theorem chunk_mem6_5_2 : ∀ p ∈ RadiusFivePruning.final6_5_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_5_2, List.forall_mem_cons]
  exact ⟨patch_mem6_5_2_0,⟨patch_mem6_5_2_1,⟨patch_mem6_5_2_2,⟨patch_mem6_5_2_5,⟨patch_mem6_5_2_6,⟨patch_mem6_5_2_7,⟨patch_mem6_5_2_8,⟨patch_mem6_5_2_9,⟨patch_mem6_5_2_10,⟨patch_mem6_5_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_5_3_0 : RadiusFivePruning.stateRow6_5_3_0 = ParentOwnership.parentRow1012 := by rfl
theorem patch_mem6_5_3_0 : RadiusFivePruning.patch6_5_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1012, parentRow_mem1012, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1012_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_3_0]
  rfl
theorem row_eq6_5_3_1 : RadiusFivePruning.stateRow6_5_3_1 = ParentOwnership.parentRow1338 := by rfl
theorem patch_mem6_5_3_1 : RadiusFivePruning.patch6_5_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1338, parentRow_mem1338, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1338_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_3_1]
  rfl
theorem row_eq6_5_3_4 : RadiusFivePruning.stateRow6_5_3_4 = ParentOwnership.parentRow0692 := by rfl
theorem patch_mem6_5_3_4 : RadiusFivePruning.patch6_5_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0692, parentRow_mem0692, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0692_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_3_4]
  rfl
theorem row_eq6_5_3_5 : RadiusFivePruning.stateRow6_5_3_5 = ParentOwnership.parentRow0691 := by rfl
theorem patch_mem6_5_3_5 : RadiusFivePruning.patch6_5_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0691, parentRow_mem0691, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0691_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_3_5]
  rfl
theorem row_eq6_5_3_6 : RadiusFivePruning.stateRow6_5_3_6 = ParentOwnership.parentRow1363 := by rfl
theorem patch_mem6_5_3_6 : RadiusFivePruning.patch6_5_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1363, parentRow_mem1363, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1363_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_3_6]
  rfl
theorem row_eq6_5_3_7 : RadiusFivePruning.stateRow6_5_3_7 = ParentOwnership.parentRow1364 := by rfl
theorem patch_mem6_5_3_7 : RadiusFivePruning.patch6_5_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1364, parentRow_mem1364, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1364_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_3_7]
  rfl
theorem row_eq6_5_3_8 : RadiusFivePruning.stateRow6_5_3_8 = ParentOwnership.parentRow1339 := by rfl
theorem patch_mem6_5_3_8 : RadiusFivePruning.patch6_5_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1339, parentRow_mem1339, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1339_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_3_8]
  rfl
theorem row_eq6_5_3_9 : RadiusFivePruning.stateRow6_5_3_9 = ParentOwnership.parentRow1340 := by rfl
theorem patch_mem6_5_3_9 : RadiusFivePruning.patch6_5_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1340, parentRow_mem1340, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1340_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_3_9]
  rfl
theorem row_eq6_5_3_10 : RadiusFivePruning.stateRow6_5_3_10 = ParentOwnership.parentRow0693 := by rfl
theorem patch_mem6_5_3_10 : RadiusFivePruning.patch6_5_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0693, parentRow_mem0693, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0693_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_3_10]
  rfl
theorem row_eq6_5_3_11 : RadiusFivePruning.stateRow6_5_3_11 = ParentOwnership.parentRow0695 := by rfl
theorem patch_mem6_5_3_11 : RadiusFivePruning.patch6_5_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0695, parentRow_mem0695, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0695_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_5_3_11]
  rfl
theorem chunk_mem6_5_3 : ∀ p ∈ RadiusFivePruning.final6_5_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_5_3, List.forall_mem_cons]
  exact ⟨patch_mem6_5_3_0,⟨patch_mem6_5_3_1,⟨patch_mem6_5_3_4,⟨patch_mem6_5_3_5,⟨patch_mem6_5_3_6,⟨patch_mem6_5_3_7,⟨patch_mem6_5_3_8,⟨patch_mem6_5_3_9,⟨patch_mem6_5_3_10,⟨patch_mem6_5_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
