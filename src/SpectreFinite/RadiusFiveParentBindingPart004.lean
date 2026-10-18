module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock0T3C1
public import SpectreFinite.RadiusFivePruningLiteralBlock0T3C2
public import SpectreFinite.RadiusFivePruningLiteralBlock0T3C3
public import SpectreFinite.RadiusFivePruningLiteralBlock0T3C4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq0_3_1_0 : RadiusFivePruning.stateRow0_3_1_0 = ParentOwnership.parentRow0641 := by rfl
theorem patch_mem0_3_1_0 : RadiusFivePruning.patch0_3_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0641, parentRow_mem0641, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0641_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_1_0]
  rfl
theorem row_eq0_3_1_2 : RadiusFivePruning.stateRow0_3_1_2 = ParentOwnership.parentRow1329 := by rfl
theorem patch_mem0_3_1_2 : RadiusFivePruning.patch0_3_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1329, parentRow_mem1329, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1329_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_1_2]
  rfl
theorem row_eq0_3_1_4 : RadiusFivePruning.stateRow0_3_1_4 = ParentOwnership.parentRow1330 := by rfl
theorem patch_mem0_3_1_4 : RadiusFivePruning.patch0_3_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1330, parentRow_mem1330, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1330_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_1_4]
  rfl
theorem row_eq0_3_1_5 : RadiusFivePruning.stateRow0_3_1_5 = ParentOwnership.parentRow1334 := by rfl
theorem patch_mem0_3_1_5 : RadiusFivePruning.patch0_3_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1334, parentRow_mem1334, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1334_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_1_5]
  rfl
theorem row_eq0_3_1_6 : RadiusFivePruning.stateRow0_3_1_6 = ParentOwnership.parentRow1331 := by rfl
theorem patch_mem0_3_1_6 : RadiusFivePruning.patch0_3_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1331, parentRow_mem1331, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1331_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_1_6]
  rfl
theorem row_eq0_3_1_9 : RadiusFivePruning.stateRow0_3_1_9 = ParentOwnership.parentRow1332 := by rfl
theorem patch_mem0_3_1_9 : RadiusFivePruning.patch0_3_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1332, parentRow_mem1332, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1332_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_1_9]
  rfl
theorem row_eq0_3_1_11 : RadiusFivePruning.stateRow0_3_1_11 = ParentOwnership.parentRow1333 := by rfl
theorem patch_mem0_3_1_11 : RadiusFivePruning.patch0_3_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1333, parentRow_mem1333, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1333_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_1_11]
  rfl
theorem chunk_mem0_3_1 : ∀ p ∈ RadiusFivePruning.final0_3_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_3_1, List.forall_mem_cons]
  exact ⟨patch_mem0_3_1_0,⟨patch_mem0_3_1_2,⟨patch_mem0_3_1_4,⟨patch_mem0_3_1_5,⟨patch_mem0_3_1_6,⟨patch_mem0_3_1_9,⟨patch_mem0_3_1_11,by simp⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_3_2_0 : RadiusFivePruning.stateRow0_3_2_0 = ParentOwnership.parentRow1344 := by rfl
theorem patch_mem0_3_2_0 : RadiusFivePruning.patch0_3_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1344, parentRow_mem1344, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1344_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_2_0]
  rfl
theorem row_eq0_3_2_1 : RadiusFivePruning.stateRow0_3_2_1 = ParentOwnership.parentRow1379 := by rfl
theorem patch_mem0_3_2_1 : RadiusFivePruning.patch0_3_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1379, parentRow_mem1379, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1379_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_2_1]
  rfl
theorem row_eq0_3_2_2 : RadiusFivePruning.stateRow0_3_2_2 = ParentOwnership.parentRow1382 := by rfl
theorem patch_mem0_3_2_2 : RadiusFivePruning.patch0_3_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1382, parentRow_mem1382, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1382_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_2_2]
  rfl
theorem row_eq0_3_2_3 : RadiusFivePruning.stateRow0_3_2_3 = ParentOwnership.parentRow1346 := by rfl
theorem patch_mem0_3_2_3 : RadiusFivePruning.patch0_3_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1346, parentRow_mem1346, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1346_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_2_3]
  rfl
theorem row_eq0_3_2_5 : RadiusFivePruning.stateRow0_3_2_5 = ParentOwnership.parentRow1343 := by rfl
theorem patch_mem0_3_2_5 : RadiusFivePruning.patch0_3_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1343, parentRow_mem1343, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1343_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_2_5]
  rfl
theorem row_eq0_3_2_6 : RadiusFivePruning.stateRow0_3_2_6 = ParentOwnership.parentRow1815 := by rfl
theorem patch_mem0_3_2_6 : RadiusFivePruning.patch0_3_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1815, parentRow_mem1815, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1815_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_2_6]
  rfl
theorem row_eq0_3_2_7 : RadiusFivePruning.stateRow0_3_2_7 = ParentOwnership.parentRow1378 := by rfl
theorem patch_mem0_3_2_7 : RadiusFivePruning.patch0_3_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1378, parentRow_mem1378, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1378_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_2_7]
  rfl
theorem row_eq0_3_2_8 : RadiusFivePruning.stateRow0_3_2_8 = ParentOwnership.parentRow1381 := by rfl
theorem patch_mem0_3_2_8 : RadiusFivePruning.patch0_3_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1381, parentRow_mem1381, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1381_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_2_8]
  rfl
theorem row_eq0_3_2_9 : RadiusFivePruning.stateRow0_3_2_9 = ParentOwnership.parentRow1345 := by rfl
theorem patch_mem0_3_2_9 : RadiusFivePruning.patch0_3_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1345, parentRow_mem1345, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1345_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_2_9]
  rfl
theorem row_eq0_3_2_10 : RadiusFivePruning.stateRow0_3_2_10 = ParentOwnership.parentRow1820 := by rfl
theorem patch_mem0_3_2_10 : RadiusFivePruning.patch0_3_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1820, parentRow_mem1820, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1820_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_2_10]
  rfl
theorem chunk_mem0_3_2 : ∀ p ∈ RadiusFivePruning.final0_3_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_3_2, List.forall_mem_cons]
  exact ⟨patch_mem0_3_2_0,⟨patch_mem0_3_2_1,⟨patch_mem0_3_2_2,⟨patch_mem0_3_2_3,⟨patch_mem0_3_2_5,⟨patch_mem0_3_2_6,⟨patch_mem0_3_2_7,⟨patch_mem0_3_2_8,⟨patch_mem0_3_2_9,⟨patch_mem0_3_2_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_3_3_0 : RadiusFivePruning.stateRow0_3_3_0 = ParentOwnership.parentRow1816 := by rfl
theorem patch_mem0_3_3_0 : RadiusFivePruning.patch0_3_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1816, parentRow_mem1816, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1816_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_3_0]
  rfl
theorem row_eq0_3_3_2 : RadiusFivePruning.stateRow0_3_3_2 = ParentOwnership.parentRow1819 := by rfl
theorem patch_mem0_3_3_2 : RadiusFivePruning.patch0_3_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1819, parentRow_mem1819, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1819_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_3_2]
  rfl
theorem row_eq0_3_3_3 : RadiusFivePruning.stateRow0_3_3_3 = ParentOwnership.parentRow0634 := by rfl
theorem patch_mem0_3_3_3 : RadiusFivePruning.patch0_3_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0634, parentRow_mem0634, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0634_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_3_3]
  rfl
theorem row_eq0_3_3_4 : RadiusFivePruning.stateRow0_3_3_4 = ParentOwnership.parentRow0636 := by rfl
theorem patch_mem0_3_3_4 : RadiusFivePruning.patch0_3_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0636, parentRow_mem0636, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0636_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_3_4]
  rfl
theorem row_eq0_3_3_5 : RadiusFivePruning.stateRow0_3_3_5 = ParentOwnership.parentRow1823 := by rfl
theorem patch_mem0_3_3_5 : RadiusFivePruning.patch0_3_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1823, parentRow_mem1823, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1823_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_3_5]
  rfl
theorem row_eq0_3_3_6 : RadiusFivePruning.stateRow0_3_3_6 = ParentOwnership.parentRow0703 := by rfl
theorem patch_mem0_3_3_6 : RadiusFivePruning.patch0_3_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0703, parentRow_mem0703, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0703_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_3_6]
  rfl
theorem row_eq0_3_3_8 : RadiusFivePruning.stateRow0_3_3_8 = ParentOwnership.parentRow1817 := by rfl
theorem patch_mem0_3_3_8 : RadiusFivePruning.patch0_3_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1817, parentRow_mem1817, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1817_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_3_8]
  rfl
theorem row_eq0_3_3_9 : RadiusFivePruning.stateRow0_3_3_9 = ParentOwnership.parentRow1380 := by rfl
theorem patch_mem0_3_3_9 : RadiusFivePruning.patch0_3_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1380, parentRow_mem1380, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1380_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_3_9]
  rfl
theorem row_eq0_3_3_11 : RadiusFivePruning.stateRow0_3_3_11 = ParentOwnership.parentRow1347 := by rfl
theorem patch_mem0_3_3_11 : RadiusFivePruning.patch0_3_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1347, parentRow_mem1347, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1347_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_3_11]
  rfl
theorem chunk_mem0_3_3 : ∀ p ∈ RadiusFivePruning.final0_3_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_3_3, List.forall_mem_cons]
  exact ⟨patch_mem0_3_3_0,⟨patch_mem0_3_3_2,⟨patch_mem0_3_3_3,⟨patch_mem0_3_3_4,⟨patch_mem0_3_3_5,⟨patch_mem0_3_3_6,⟨patch_mem0_3_3_8,⟨patch_mem0_3_3_9,⟨patch_mem0_3_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_3_4_0 : RadiusFivePruning.stateRow0_3_4_0 = ParentOwnership.parentRow1821 := by rfl
theorem patch_mem0_3_4_0 : RadiusFivePruning.patch0_3_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1821, parentRow_mem1821, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1821_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_4_0]
  rfl
theorem row_eq0_3_4_1 : RadiusFivePruning.stateRow0_3_4_1 = ParentOwnership.parentRow1348 := by rfl
theorem patch_mem0_3_4_1 : RadiusFivePruning.patch0_3_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1348, parentRow_mem1348, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1348_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_4_1]
  rfl
theorem row_eq0_3_4_2 : RadiusFivePruning.stateRow0_3_4_2 = ParentOwnership.parentRow1824 := by rfl
theorem patch_mem0_3_4_2 : RadiusFivePruning.patch0_3_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1824, parentRow_mem1824, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1824_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_4_2]
  rfl
theorem row_eq0_3_4_4 : RadiusFivePruning.stateRow0_3_4_4 = ParentOwnership.parentRow1383 := by rfl
theorem patch_mem0_3_4_4 : RadiusFivePruning.patch0_3_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1383, parentRow_mem1383, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1383_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_4_4]
  rfl
theorem row_eq0_3_4_6 : RadiusFivePruning.stateRow0_3_4_6 = ParentOwnership.parentRow1813 := by rfl
theorem patch_mem0_3_4_6 : RadiusFivePruning.patch0_3_4_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1813, parentRow_mem1813, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1813_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_4_6]
  rfl
theorem row_eq0_3_4_7 : RadiusFivePruning.stateRow0_3_4_7 = ParentOwnership.parentRow1818 := by rfl
theorem patch_mem0_3_4_7 : RadiusFivePruning.patch0_3_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1818, parentRow_mem1818, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1818_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_4_7]
  rfl
theorem row_eq0_3_4_8 : RadiusFivePruning.stateRow0_3_4_8 = ParentOwnership.parentRow0633 := by rfl
theorem patch_mem0_3_4_8 : RadiusFivePruning.patch0_3_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0633, parentRow_mem0633, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0633_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_4_8]
  rfl
theorem row_eq0_3_4_9 : RadiusFivePruning.stateRow0_3_4_9 = ParentOwnership.parentRow0635 := by rfl
theorem patch_mem0_3_4_9 : RadiusFivePruning.patch0_3_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0635, parentRow_mem0635, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0635_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_4_9]
  rfl
theorem row_eq0_3_4_10 : RadiusFivePruning.stateRow0_3_4_10 = ParentOwnership.parentRow1822 := by rfl
theorem patch_mem0_3_4_10 : RadiusFivePruning.patch0_3_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1822, parentRow_mem1822, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1822_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_4_10]
  rfl
theorem chunk_mem0_3_4 : ∀ p ∈ RadiusFivePruning.final0_3_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_3_4, List.forall_mem_cons]
  exact ⟨patch_mem0_3_4_0,⟨patch_mem0_3_4_1,⟨patch_mem0_3_4_2,⟨patch_mem0_3_4_4,⟨patch_mem0_3_4_6,⟨patch_mem0_3_4_7,⟨patch_mem0_3_4_8,⟨patch_mem0_3_4_9,⟨patch_mem0_3_4_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
