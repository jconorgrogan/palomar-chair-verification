module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock6T1C0
public import SpectreFinite.RadiusFivePruningLiteralBlock6T1C1
public import SpectreFinite.RadiusFivePruningLiteralBlock6T1C2
public import SpectreFinite.RadiusFivePruningLiteralBlock6T1C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq6_1_0_2 : RadiusFivePruning.stateRow6_1_0_2 = ParentOwnership.parentRow1808 := by rfl
theorem patch_mem6_1_0_2 : RadiusFivePruning.patch6_1_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1808, parentRow_mem1808, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1808_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_0_2]
  rfl
theorem row_eq6_1_0_3 : RadiusFivePruning.stateRow6_1_0_3 = ParentOwnership.parentRow0626 := by rfl
theorem patch_mem6_1_0_3 : RadiusFivePruning.patch6_1_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0626, parentRow_mem0626, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0626_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_0_3]
  rfl
theorem row_eq6_1_0_5 : RadiusFivePruning.stateRow6_1_0_5 = ParentOwnership.parentRow0638 := by rfl
theorem patch_mem6_1_0_5 : RadiusFivePruning.patch6_1_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0638, parentRow_mem0638, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0638_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_0_5]
  rfl
theorem row_eq6_1_0_6 : RadiusFivePruning.stateRow6_1_0_6 = ParentOwnership.parentRow0637 := by rfl
theorem patch_mem6_1_0_6 : RadiusFivePruning.patch6_1_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0637, parentRow_mem0637, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0637_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_0_6]
  rfl
theorem row_eq6_1_0_8 : RadiusFivePruning.stateRow6_1_0_8 = ParentOwnership.parentRow1317 := by rfl
theorem patch_mem6_1_0_8 : RadiusFivePruning.patch6_1_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1317, parentRow_mem1317, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1317_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_0_8]
  rfl
theorem row_eq6_1_0_10 : RadiusFivePruning.stateRow6_1_0_10 = ParentOwnership.parentRow1310 := by rfl
theorem patch_mem6_1_0_10 : RadiusFivePruning.patch6_1_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1310, parentRow_mem1310, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1310_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_0_10]
  rfl
theorem chunk_mem6_1_0 : ∀ p ∈ RadiusFivePruning.final6_1_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_1_0, List.forall_mem_cons]
  exact ⟨patch_mem6_1_0_2,⟨patch_mem6_1_0_3,⟨patch_mem6_1_0_5,⟨patch_mem6_1_0_6,⟨patch_mem6_1_0_8,⟨patch_mem6_1_0_10,by simp⟩⟩⟩⟩⟩⟩
theorem row_eq6_1_1_0 : RadiusFivePruning.stateRow6_1_1_0 = ParentOwnership.parentRow1342 := by rfl
theorem patch_mem6_1_1_0 : RadiusFivePruning.patch6_1_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1342, parentRow_mem1342, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1342_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_1_0]
  rfl
theorem row_eq6_1_1_3 : RadiusFivePruning.stateRow6_1_1_3 = ParentOwnership.parentRow1802 := by rfl
theorem patch_mem6_1_1_3 : RadiusFivePruning.patch6_1_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1802, parentRow_mem1802, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1802_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_1_3]
  rfl
theorem row_eq6_1_1_4 : RadiusFivePruning.stateRow6_1_1_4 = ParentOwnership.parentRow1803 := by rfl
theorem patch_mem6_1_1_4 : RadiusFivePruning.patch6_1_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1803, parentRow_mem1803, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1803_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_1_4]
  rfl
theorem row_eq6_1_1_5 : RadiusFivePruning.stateRow6_1_1_5 = ParentOwnership.parentRow1809 := by rfl
theorem patch_mem6_1_1_5 : RadiusFivePruning.patch6_1_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1809, parentRow_mem1809, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1809_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_1_5]
  rfl
theorem row_eq6_1_1_7 : RadiusFivePruning.stateRow6_1_1_7 = ParentOwnership.parentRow1324 := by rfl
theorem patch_mem6_1_1_7 : RadiusFivePruning.patch6_1_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1324, parentRow_mem1324, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1324_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_1_7]
  rfl
theorem row_eq6_1_1_8 : RadiusFivePruning.stateRow6_1_1_8 = ParentOwnership.parentRow1318 := by rfl
theorem patch_mem6_1_1_8 : RadiusFivePruning.patch6_1_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1318, parentRow_mem1318, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1318_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_1_8]
  rfl
theorem row_eq6_1_1_10 : RadiusFivePruning.stateRow6_1_1_10 = ParentOwnership.parentRow1303 := by rfl
theorem patch_mem6_1_1_10 : RadiusFivePruning.patch6_1_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1303, parentRow_mem1303, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1303_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_1_10]
  rfl
theorem row_eq6_1_1_11 : RadiusFivePruning.stateRow6_1_1_11 = ParentOwnership.parentRow1309 := by rfl
theorem patch_mem6_1_1_11 : RadiusFivePruning.patch6_1_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1309, parentRow_mem1309, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1309_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_1_11]
  rfl
theorem chunk_mem6_1_1 : ∀ p ∈ RadiusFivePruning.final6_1_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_1_1, List.forall_mem_cons]
  exact ⟨patch_mem6_1_1_0,⟨patch_mem6_1_1_3,⟨patch_mem6_1_1_4,⟨patch_mem6_1_1_5,⟨patch_mem6_1_1_7,⟨patch_mem6_1_1_8,⟨patch_mem6_1_1_10,⟨patch_mem6_1_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_1_2_0 : RadiusFivePruning.stateRow6_1_2_0 = ParentOwnership.parentRow1312 := by rfl
theorem patch_mem6_1_2_0 : RadiusFivePruning.patch6_1_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1312, parentRow_mem1312, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1312_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_2_0]
  rfl
theorem row_eq6_1_2_1 : RadiusFivePruning.stateRow6_1_2_1 = ParentOwnership.parentRow1313 := by rfl
theorem patch_mem6_1_2_1 : RadiusFivePruning.patch6_1_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1313, parentRow_mem1313, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1313_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_2_1]
  rfl
theorem row_eq6_1_2_2 : RadiusFivePruning.stateRow6_1_2_2 = ParentOwnership.parentRow1311 := by rfl
theorem patch_mem6_1_2_2 : RadiusFivePruning.patch6_1_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1311, parentRow_mem1311, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1311_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_2_2]
  rfl
theorem row_eq6_1_2_5 : RadiusFivePruning.stateRow6_1_2_5 = ParentOwnership.parentRow1316 := by rfl
theorem patch_mem6_1_2_5 : RadiusFivePruning.patch6_1_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1316, parentRow_mem1316, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1316_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_2_5]
  rfl
theorem row_eq6_1_2_6 : RadiusFivePruning.stateRow6_1_2_6 = ParentOwnership.parentRow1806 := by rfl
theorem patch_mem6_1_2_6 : RadiusFivePruning.patch6_1_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1806, parentRow_mem1806, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1806_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_2_6]
  rfl
theorem row_eq6_1_2_7 : RadiusFivePruning.stateRow6_1_2_7 = ParentOwnership.parentRow1807 := by rfl
theorem patch_mem6_1_2_7 : RadiusFivePruning.patch6_1_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1807, parentRow_mem1807, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1807_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_2_7]
  rfl
theorem row_eq6_1_2_8 : RadiusFivePruning.stateRow6_1_2_8 = ParentOwnership.parentRow1812 := by rfl
theorem patch_mem6_1_2_8 : RadiusFivePruning.patch6_1_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1812, parentRow_mem1812, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1812_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_2_8]
  rfl
theorem row_eq6_1_2_9 : RadiusFivePruning.stateRow6_1_2_9 = ParentOwnership.parentRow1804 := by rfl
theorem patch_mem6_1_2_9 : RadiusFivePruning.patch6_1_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1804, parentRow_mem1804, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1804_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_2_9]
  rfl
theorem row_eq6_1_2_10 : RadiusFivePruning.stateRow6_1_2_10 = ParentOwnership.parentRow1805 := by rfl
theorem patch_mem6_1_2_10 : RadiusFivePruning.patch6_1_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1805, parentRow_mem1805, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1805_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_2_10]
  rfl
theorem row_eq6_1_2_11 : RadiusFivePruning.stateRow6_1_2_11 = ParentOwnership.parentRow1810 := by rfl
theorem patch_mem6_1_2_11 : RadiusFivePruning.patch6_1_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1810, parentRow_mem1810, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1810_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_2_11]
  rfl
theorem chunk_mem6_1_2 : ∀ p ∈ RadiusFivePruning.final6_1_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_1_2, List.forall_mem_cons]
  exact ⟨patch_mem6_1_2_0,⟨patch_mem6_1_2_1,⟨patch_mem6_1_2_2,⟨patch_mem6_1_2_5,⟨patch_mem6_1_2_6,⟨patch_mem6_1_2_7,⟨patch_mem6_1_2_8,⟨patch_mem6_1_2_9,⟨patch_mem6_1_2_10,⟨patch_mem6_1_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_1_3_0 : RadiusFivePruning.stateRow6_1_3_0 = ParentOwnership.parentRow1811 := by rfl
theorem patch_mem6_1_3_0 : RadiusFivePruning.patch6_1_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1811, parentRow_mem1811, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1811_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_3_0]
  rfl
theorem row_eq6_1_3_1 : RadiusFivePruning.stateRow6_1_3_1 = ParentOwnership.parentRow0294 := by rfl
theorem patch_mem6_1_3_1 : RadiusFivePruning.patch6_1_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0294, parentRow_mem0294, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0294_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_3_1]
  rfl
theorem row_eq6_1_3_4 : RadiusFivePruning.stateRow6_1_3_4 = ParentOwnership.parentRow0291 := by rfl
theorem patch_mem6_1_3_4 : RadiusFivePruning.patch6_1_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0291, parentRow_mem0291, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0291_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_3_4]
  rfl
theorem row_eq6_1_3_5 : RadiusFivePruning.stateRow6_1_3_5 = ParentOwnership.parentRow0300 := by rfl
theorem patch_mem6_1_3_5 : RadiusFivePruning.patch6_1_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0300, parentRow_mem0300, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0300_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_3_5]
  rfl
theorem row_eq6_1_3_6 : RadiusFivePruning.stateRow6_1_3_6 = ParentOwnership.parentRow0289 := by rfl
theorem patch_mem6_1_3_6 : RadiusFivePruning.patch6_1_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0289, parentRow_mem0289, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0289_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_3_6]
  rfl
theorem row_eq6_1_3_7 : RadiusFivePruning.stateRow6_1_3_7 = ParentOwnership.parentRow0292 := by rfl
theorem patch_mem6_1_3_7 : RadiusFivePruning.patch6_1_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0292, parentRow_mem0292, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0292_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_3_7]
  rfl
theorem row_eq6_1_3_8 : RadiusFivePruning.stateRow6_1_3_8 = ParentOwnership.parentRow0290 := by rfl
theorem patch_mem6_1_3_8 : RadiusFivePruning.patch6_1_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0290, parentRow_mem0290, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0290_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_3_8]
  rfl
theorem row_eq6_1_3_9 : RadiusFivePruning.stateRow6_1_3_9 = ParentOwnership.parentRow0293 := by rfl
theorem patch_mem6_1_3_9 : RadiusFivePruning.patch6_1_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0293, parentRow_mem0293, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0293_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_3_9]
  rfl
theorem row_eq6_1_3_10 : RadiusFivePruning.stateRow6_1_3_10 = ParentOwnership.parentRow1325 := by rfl
theorem patch_mem6_1_3_10 : RadiusFivePruning.patch6_1_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1325, parentRow_mem1325, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1325_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_3_10]
  rfl
theorem row_eq6_1_3_11 : RadiusFivePruning.stateRow6_1_3_11 = ParentOwnership.parentRow1326 := by rfl
theorem patch_mem6_1_3_11 : RadiusFivePruning.patch6_1_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1326, parentRow_mem1326, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1326_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_1_3_11]
  rfl
theorem chunk_mem6_1_3 : ∀ p ∈ RadiusFivePruning.final6_1_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_1_3, List.forall_mem_cons]
  exact ⟨patch_mem6_1_3_0,⟨patch_mem6_1_3_1,⟨patch_mem6_1_3_4,⟨patch_mem6_1_3_5,⟨patch_mem6_1_3_6,⟨patch_mem6_1_3_7,⟨patch_mem6_1_3_8,⟨patch_mem6_1_3_9,⟨patch_mem6_1_3_10,⟨patch_mem6_1_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
