module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock8T4C4
public import SpectreFinite.RadiusFivePruningLiteralBlock8T4C5
public import SpectreFinite.RadiusFivePruningLiteralBlock8T5C0
public import SpectreFinite.RadiusFivePruningLiteralBlock8T5C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq8_4_4_0 : RadiusFivePruning.stateRow8_4_4_0 = ParentOwnership.parentRow1836 := by rfl
theorem patch_mem8_4_4_0 : RadiusFivePruning.patch8_4_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1836, parentRow_mem1836, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1836_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_4_0]
  rfl
theorem row_eq8_4_4_1 : RadiusFivePruning.stateRow8_4_4_1 = ParentOwnership.parentRow0674 := by rfl
theorem patch_mem8_4_4_1 : RadiusFivePruning.patch8_4_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0674, parentRow_mem0674, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0674_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_4_1]
  rfl
theorem row_eq8_4_4_2 : RadiusFivePruning.stateRow8_4_4_2 = ParentOwnership.parentRow1841 := by rfl
theorem patch_mem8_4_4_2 : RadiusFivePruning.patch8_4_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1841, parentRow_mem1841, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1841_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_4_2]
  rfl
theorem row_eq8_4_4_3 : RadiusFivePruning.stateRow8_4_4_3 = ParentOwnership.parentRow0675 := by rfl
theorem patch_mem8_4_4_3 : RadiusFivePruning.patch8_4_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0675, parentRow_mem0675, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0675_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_4_3]
  rfl
theorem row_eq8_4_4_4 : RadiusFivePruning.stateRow8_4_4_4 = ParentOwnership.parentRow1842 := by rfl
theorem patch_mem8_4_4_4 : RadiusFivePruning.patch8_4_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1842, parentRow_mem1842, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1842_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_4_4]
  rfl
theorem row_eq8_4_4_5 : RadiusFivePruning.stateRow8_4_4_5 = ParentOwnership.parentRow1847 := by rfl
theorem patch_mem8_4_4_5 : RadiusFivePruning.patch8_4_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1847, parentRow_mem1847, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1847_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_4_5]
  rfl
theorem row_eq8_4_4_8 : RadiusFivePruning.stateRow8_4_4_8 = ParentOwnership.parentRow1397 := by rfl
theorem patch_mem8_4_4_8 : RadiusFivePruning.patch8_4_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1397, parentRow_mem1397, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1397_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_4_8]
  rfl
theorem row_eq8_4_4_9 : RadiusFivePruning.stateRow8_4_4_9 = ParentOwnership.parentRow1845 := by rfl
theorem patch_mem8_4_4_9 : RadiusFivePruning.patch8_4_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1845, parentRow_mem1845, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1845_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_4_9]
  rfl
theorem row_eq8_4_4_10 : RadiusFivePruning.stateRow8_4_4_10 = ParentOwnership.parentRow1850 := by rfl
theorem patch_mem8_4_4_10 : RadiusFivePruning.patch8_4_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1850, parentRow_mem1850, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1850_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_4_10]
  rfl
theorem row_eq8_4_4_11 : RadiusFivePruning.stateRow8_4_4_11 = ParentOwnership.parentRow1846 := by rfl
theorem patch_mem8_4_4_11 : RadiusFivePruning.patch8_4_4_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1846, parentRow_mem1846, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1846_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_4_11]
  rfl
theorem chunk_mem8_4_4 : ∀ p ∈ RadiusFivePruning.final8_4_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_4_4, List.forall_mem_cons]
  exact ⟨patch_mem8_4_4_0,⟨patch_mem8_4_4_1,⟨patch_mem8_4_4_2,⟨patch_mem8_4_4_3,⟨patch_mem8_4_4_4,⟨patch_mem8_4_4_5,⟨patch_mem8_4_4_8,⟨patch_mem8_4_4_9,⟨patch_mem8_4_4_10,⟨patch_mem8_4_4_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_4_5_0 : RadiusFivePruning.stateRow8_4_5_0 = ParentOwnership.parentRow1851 := by rfl
theorem patch_mem8_4_5_0 : RadiusFivePruning.patch8_4_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1851, parentRow_mem1851, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1851_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_5_0]
  rfl
theorem row_eq8_4_5_1 : RadiusFivePruning.stateRow8_4_5_1 = ParentOwnership.parentRow0673 := by rfl
theorem patch_mem8_4_5_1 : RadiusFivePruning.patch8_4_5_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0673, parentRow_mem0673, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0673_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_5_1]
  rfl
theorem row_eq8_4_5_2 : RadiusFivePruning.stateRow8_4_5_2 = ParentOwnership.parentRow1839 := by rfl
theorem patch_mem8_4_5_2 : RadiusFivePruning.patch8_4_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1839, parentRow_mem1839, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1839_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_5_2]
  rfl
theorem row_eq8_4_5_3 : RadiusFivePruning.stateRow8_4_5_3 = ParentOwnership.parentRow1840 := by rfl
theorem patch_mem8_4_5_3 : RadiusFivePruning.patch8_4_5_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1840, parentRow_mem1840, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1840_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_5_3]
  rfl
theorem row_eq8_4_5_4 : RadiusFivePruning.stateRow8_4_5_4 = ParentOwnership.parentRow1424 := by rfl
theorem patch_mem8_4_5_4 : RadiusFivePruning.patch8_4_5_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1424, parentRow_mem1424, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1424_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_5_4]
  rfl
theorem row_eq8_4_5_5 : RadiusFivePruning.stateRow8_4_5_5 = ParentOwnership.parentRow1394 := by rfl
theorem patch_mem8_4_5_5 : RadiusFivePruning.patch8_4_5_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1394, parentRow_mem1394, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1394_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_5_5]
  rfl
theorem row_eq8_4_5_6 : RadiusFivePruning.stateRow8_4_5_6 = ParentOwnership.parentRow1843 := by rfl
theorem patch_mem8_4_5_6 : RadiusFivePruning.patch8_4_5_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1843, parentRow_mem1843, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1843_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_5_6]
  rfl
theorem row_eq8_4_5_7 : RadiusFivePruning.stateRow8_4_5_7 = ParentOwnership.parentRow1848 := by rfl
theorem patch_mem8_4_5_7 : RadiusFivePruning.patch8_4_5_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1848, parentRow_mem1848, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1848_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_5_7]
  rfl
theorem row_eq8_4_5_8 : RadiusFivePruning.stateRow8_4_5_8 = ParentOwnership.parentRow1844 := by rfl
theorem patch_mem8_4_5_8 : RadiusFivePruning.patch8_4_5_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1844, parentRow_mem1844, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1844_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_5_8]
  rfl
theorem row_eq8_4_5_9 : RadiusFivePruning.stateRow8_4_5_9 = ParentOwnership.parentRow1849 := by rfl
theorem patch_mem8_4_5_9 : RadiusFivePruning.patch8_4_5_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1849, parentRow_mem1849, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1849_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_5_9]
  rfl
theorem chunk_mem8_4_5 : ∀ p ∈ RadiusFivePruning.final8_4_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_4_5, List.forall_mem_cons]
  exact ⟨patch_mem8_4_5_0,⟨patch_mem8_4_5_1,⟨patch_mem8_4_5_2,⟨patch_mem8_4_5_3,⟨patch_mem8_4_5_4,⟨patch_mem8_4_5_5,⟨patch_mem8_4_5_6,⟨patch_mem8_4_5_7,⟨patch_mem8_4_5_8,⟨patch_mem8_4_5_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_5_0_1 : RadiusFivePruning.stateRow8_5_0_1 = ParentOwnership.parentRow0418 := by rfl
theorem patch_mem8_5_0_1 : RadiusFivePruning.patch8_5_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0418, parentRow_mem0418, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0418_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_0_1]
  rfl
theorem row_eq8_5_0_3 : RadiusFivePruning.stateRow8_5_0_3 = ParentOwnership.parentRow1532 := by rfl
theorem patch_mem8_5_0_3 : RadiusFivePruning.patch8_5_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1532, parentRow_mem1532, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1532_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_0_3]
  rfl
theorem row_eq8_5_0_4 : RadiusFivePruning.stateRow8_5_0_4 = ParentOwnership.parentRow0419 := by rfl
theorem patch_mem8_5_0_4 : RadiusFivePruning.patch8_5_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0419, parentRow_mem0419, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0419_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_0_4]
  rfl
theorem row_eq8_5_0_5 : RadiusFivePruning.stateRow8_5_0_5 = ParentOwnership.parentRow1154 := by rfl
theorem patch_mem8_5_0_5 : RadiusFivePruning.patch8_5_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1154, parentRow_mem1154, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1154_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_0_5]
  rfl
theorem row_eq8_5_0_6 : RadiusFivePruning.stateRow8_5_0_6 = ParentOwnership.parentRow0225 := by rfl
theorem patch_mem8_5_0_6 : RadiusFivePruning.patch8_5_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0225, parentRow_mem0225, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0225_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_0_6]
  rfl
theorem row_eq8_5_0_7 : RadiusFivePruning.stateRow8_5_0_7 = ParentOwnership.parentRow0421 := by rfl
theorem patch_mem8_5_0_7 : RadiusFivePruning.patch8_5_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0421, parentRow_mem0421, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0421_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_0_7]
  rfl
theorem row_eq8_5_0_8 : RadiusFivePruning.stateRow8_5_0_8 = ParentOwnership.parentRow0422 := by rfl
theorem patch_mem8_5_0_8 : RadiusFivePruning.patch8_5_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0422, parentRow_mem0422, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0422_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_0_8]
  rfl
theorem row_eq8_5_0_9 : RadiusFivePruning.stateRow8_5_0_9 = ParentOwnership.parentRow0420 := by rfl
theorem patch_mem8_5_0_9 : RadiusFivePruning.patch8_5_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0420, parentRow_mem0420, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0420_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_0_9]
  rfl
theorem row_eq8_5_0_10 : RadiusFivePruning.stateRow8_5_0_10 = ParentOwnership.parentRow1156 := by rfl
theorem patch_mem8_5_0_10 : RadiusFivePruning.patch8_5_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1156, parentRow_mem1156, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1156_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_0_10]
  rfl
theorem row_eq8_5_0_11 : RadiusFivePruning.stateRow8_5_0_11 = ParentOwnership.parentRow1155 := by rfl
theorem patch_mem8_5_0_11 : RadiusFivePruning.patch8_5_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1155, parentRow_mem1155, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1155_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_0_11]
  rfl
theorem chunk_mem8_5_0 : ∀ p ∈ RadiusFivePruning.final8_5_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_5_0, List.forall_mem_cons]
  exact ⟨patch_mem8_5_0_1,⟨patch_mem8_5_0_3,⟨patch_mem8_5_0_4,⟨patch_mem8_5_0_5,⟨patch_mem8_5_0_6,⟨patch_mem8_5_0_7,⟨patch_mem8_5_0_8,⟨patch_mem8_5_0_9,⟨patch_mem8_5_0_10,⟨patch_mem8_5_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_5_1_0 : RadiusFivePruning.stateRow8_5_1_0 = ParentOwnership.parentRow1157 := by rfl
theorem patch_mem8_5_1_0 : RadiusFivePruning.patch8_5_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1157, parentRow_mem1157, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1157_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_1_0]
  rfl
theorem row_eq8_5_1_1 : RadiusFivePruning.stateRow8_5_1_1 = ParentOwnership.parentRow1158 := by rfl
theorem patch_mem8_5_1_1 : RadiusFivePruning.patch8_5_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1158, parentRow_mem1158, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1158_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_1_1]
  rfl
theorem row_eq8_5_1_2 : RadiusFivePruning.stateRow8_5_1_2 = ParentOwnership.parentRow0227 := by rfl
theorem patch_mem8_5_1_2 : RadiusFivePruning.patch8_5_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0227, parentRow_mem0227, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0227_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_1_2]
  rfl
theorem row_eq8_5_1_3 : RadiusFivePruning.stateRow8_5_1_3 = ParentOwnership.parentRow0226 := by rfl
theorem patch_mem8_5_1_3 : RadiusFivePruning.patch8_5_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0226, parentRow_mem0226, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0226_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_1_3]
  rfl
theorem row_eq8_5_1_4 : RadiusFivePruning.stateRow8_5_1_4 = ParentOwnership.parentRow0228 := by rfl
theorem patch_mem8_5_1_4 : RadiusFivePruning.patch8_5_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0228, parentRow_mem0228, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0228_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_1_4]
  rfl
theorem row_eq8_5_1_6 : RadiusFivePruning.stateRow8_5_1_6 = ParentOwnership.parentRow0423 := by rfl
theorem patch_mem8_5_1_6 : RadiusFivePruning.patch8_5_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0423, parentRow_mem0423, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0423_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_1_6]
  rfl
theorem row_eq8_5_1_8 : RadiusFivePruning.stateRow8_5_1_8 = ParentOwnership.parentRow0425 := by rfl
theorem patch_mem8_5_1_8 : RadiusFivePruning.patch8_5_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0425, parentRow_mem0425, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0425_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_1_8]
  rfl
theorem row_eq8_5_1_9 : RadiusFivePruning.stateRow8_5_1_9 = ParentOwnership.parentRow1540 := by rfl
theorem patch_mem8_5_1_9 : RadiusFivePruning.patch8_5_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1540, parentRow_mem1540, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1540_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_1_9]
  rfl
theorem row_eq8_5_1_10 : RadiusFivePruning.stateRow8_5_1_10 = ParentOwnership.parentRow1541 := by rfl
theorem patch_mem8_5_1_10 : RadiusFivePruning.patch8_5_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1541, parentRow_mem1541, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1541_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_5_1_10]
  rfl
theorem chunk_mem8_5_1 : ∀ p ∈ RadiusFivePruning.final8_5_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_5_1, List.forall_mem_cons]
  exact ⟨patch_mem8_5_1_0,⟨patch_mem8_5_1_1,⟨patch_mem8_5_1_2,⟨patch_mem8_5_1_3,⟨patch_mem8_5_1_4,⟨patch_mem8_5_1_6,⟨patch_mem8_5_1_8,⟨patch_mem8_5_1_9,⟨patch_mem8_5_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
