module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock0T1C3
public import SpectreFinite.RadiusFivePruningLiteralBlock0T1C4
public import SpectreFinite.RadiusFivePruningLiteralBlock0T2C0
public import SpectreFinite.RadiusFivePruningLiteralBlock0T2C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq0_1_3_0 : RadiusFivePruning.stateRow0_1_3_0 = ParentOwnership.parentRow1682 := by rfl
theorem patch_mem0_1_3_0 : RadiusFivePruning.patch0_1_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1682, parentRow_mem1682, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1682_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_3_0]
  rfl
theorem row_eq0_1_3_2 : RadiusFivePruning.stateRow0_1_3_2 = ParentOwnership.parentRow1708 := by rfl
theorem patch_mem0_1_3_2 : RadiusFivePruning.patch0_1_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1708, parentRow_mem1708, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1708_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_3_2]
  rfl
theorem row_eq0_1_3_3 : RadiusFivePruning.stateRow0_1_3_3 = ParentOwnership.parentRow1693 := by rfl
theorem patch_mem0_1_3_3 : RadiusFivePruning.patch0_1_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1693, parentRow_mem1693, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1693_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_3_3]
  rfl
theorem row_eq0_1_3_4 : RadiusFivePruning.stateRow0_1_3_4 = ParentOwnership.parentRow1710 := by rfl
theorem patch_mem0_1_3_4 : RadiusFivePruning.patch0_1_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1710, parentRow_mem1710, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1710_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_3_4]
  rfl
theorem row_eq0_1_3_5 : RadiusFivePruning.stateRow0_1_3_5 = ParentOwnership.parentRow1709 := by rfl
theorem patch_mem0_1_3_5 : RadiusFivePruning.patch0_1_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1709, parentRow_mem1709, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1709_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_3_5]
  rfl
theorem row_eq0_1_3_6 : RadiusFivePruning.stateRow0_1_3_6 = ParentOwnership.parentRow1712 := by rfl
theorem patch_mem0_1_3_6 : RadiusFivePruning.patch0_1_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1712, parentRow_mem1712, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1712_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_3_6]
  rfl
theorem row_eq0_1_3_8 : RadiusFivePruning.stateRow0_1_3_8 = ParentOwnership.parentRow1703 := by rfl
theorem patch_mem0_1_3_8 : RadiusFivePruning.patch0_1_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1703, parentRow_mem1703, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1703_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_3_8]
  rfl
theorem row_eq0_1_3_9 : RadiusFivePruning.stateRow0_1_3_9 = ParentOwnership.parentRow1691 := by rfl
theorem patch_mem0_1_3_9 : RadiusFivePruning.patch0_1_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1691, parentRow_mem1691, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1691_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_3_9]
  rfl
theorem row_eq0_1_3_11 : RadiusFivePruning.stateRow0_1_3_11 = ParentOwnership.parentRow1699 := by rfl
theorem patch_mem0_1_3_11 : RadiusFivePruning.patch0_1_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1699, parentRow_mem1699, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1699_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_3_11]
  rfl
theorem chunk_mem0_1_3 : ∀ p ∈ RadiusFivePruning.final0_1_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_1_3, List.forall_mem_cons]
  exact ⟨patch_mem0_1_3_0,⟨patch_mem0_1_3_2,⟨patch_mem0_1_3_3,⟨patch_mem0_1_3_4,⟨patch_mem0_1_3_5,⟨patch_mem0_1_3_6,⟨patch_mem0_1_3_8,⟨patch_mem0_1_3_9,⟨patch_mem0_1_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_1_4_0 : RadiusFivePruning.stateRow0_1_4_0 = ParentOwnership.parentRow1701 := by rfl
theorem patch_mem0_1_4_0 : RadiusFivePruning.patch0_1_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1701, parentRow_mem1701, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1701_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_4_0]
  rfl
theorem row_eq0_1_4_1 : RadiusFivePruning.stateRow0_1_4_1 = ParentOwnership.parentRow1700 := by rfl
theorem patch_mem0_1_4_1 : RadiusFivePruning.patch0_1_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1700, parentRow_mem1700, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1700_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_4_1]
  rfl
theorem row_eq0_1_4_2 : RadiusFivePruning.stateRow0_1_4_2 = ParentOwnership.parentRow1702 := by rfl
theorem patch_mem0_1_4_2 : RadiusFivePruning.patch0_1_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1702, parentRow_mem1702, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1702_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_4_2]
  rfl
theorem row_eq0_1_4_4 : RadiusFivePruning.stateRow0_1_4_4 = ParentOwnership.parentRow1711 := by rfl
theorem patch_mem0_1_4_4 : RadiusFivePruning.patch0_1_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1711, parentRow_mem1711, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1711_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_4_4]
  rfl
theorem row_eq0_1_4_6 : RadiusFivePruning.stateRow0_1_4_6 = ParentOwnership.parentRow1706 := by rfl
theorem patch_mem0_1_4_6 : RadiusFivePruning.patch0_1_4_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1706, parentRow_mem1706, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1706_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_4_6]
  rfl
theorem row_eq0_1_4_7 : RadiusFivePruning.stateRow0_1_4_7 = ParentOwnership.parentRow1704 := by rfl
theorem patch_mem0_1_4_7 : RadiusFivePruning.patch0_1_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1704, parentRow_mem1704, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1704_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_4_7]
  rfl
theorem row_eq0_1_4_8 : RadiusFivePruning.stateRow0_1_4_8 = ParentOwnership.parentRow1692 := by rfl
theorem patch_mem0_1_4_8 : RadiusFivePruning.patch0_1_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1692, parentRow_mem1692, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1692_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_4_8]
  rfl
theorem row_eq0_1_4_9 : RadiusFivePruning.stateRow0_1_4_9 = ParentOwnership.parentRow1707 := by rfl
theorem patch_mem0_1_4_9 : RadiusFivePruning.patch0_1_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1707, parentRow_mem1707, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1707_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_4_9]
  rfl
theorem row_eq0_1_4_10 : RadiusFivePruning.stateRow0_1_4_10 = ParentOwnership.parentRow1705 := by rfl
theorem patch_mem0_1_4_10 : RadiusFivePruning.patch0_1_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1705, parentRow_mem1705, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1705_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_4_10]
  rfl
theorem chunk_mem0_1_4 : ∀ p ∈ RadiusFivePruning.final0_1_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_1_4, List.forall_mem_cons]
  exact ⟨patch_mem0_1_4_0,⟨patch_mem0_1_4_1,⟨patch_mem0_1_4_2,⟨patch_mem0_1_4_4,⟨patch_mem0_1_4_6,⟨patch_mem0_1_4_7,⟨patch_mem0_1_4_8,⟨patch_mem0_1_4_9,⟨patch_mem0_1_4_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_2_0_0 : RadiusFivePruning.stateRow0_2_0_0 = ParentOwnership.parentRow0885 := by rfl
theorem patch_mem0_2_0_0 : RadiusFivePruning.patch0_2_0_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0885, parentRow_mem0885, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0885_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_0_0]
  rfl
theorem row_eq0_2_0_1 : RadiusFivePruning.stateRow0_2_0_1 = ParentOwnership.parentRow1942 := by rfl
theorem patch_mem0_2_0_1 : RadiusFivePruning.patch0_2_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1942, parentRow_mem1942, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1942_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_0_1]
  rfl
theorem row_eq0_2_0_3 : RadiusFivePruning.stateRow0_2_0_3 = ParentOwnership.parentRow1938 := by rfl
theorem patch_mem0_2_0_3 : RadiusFivePruning.patch0_2_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1938, parentRow_mem1938, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1938_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_0_3]
  rfl
theorem row_eq0_2_0_4 : RadiusFivePruning.stateRow0_2_0_4 = ParentOwnership.parentRow1943 := by rfl
theorem patch_mem0_2_0_4 : RadiusFivePruning.patch0_2_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1943, parentRow_mem1943, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1943_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_0_4]
  rfl
theorem row_eq0_2_0_5 : RadiusFivePruning.stateRow0_2_0_5 = ParentOwnership.parentRow1941 := by rfl
theorem patch_mem0_2_0_5 : RadiusFivePruning.patch0_2_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1941, parentRow_mem1941, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1941_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_0_5]
  rfl
theorem row_eq0_2_0_6 : RadiusFivePruning.stateRow0_2_0_6 = ParentOwnership.parentRow0887 := by rfl
theorem patch_mem0_2_0_6 : RadiusFivePruning.patch0_2_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0887, parentRow_mem0887, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0887_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_0_6]
  rfl
theorem row_eq0_2_0_8 : RadiusFivePruning.stateRow0_2_0_8 = ParentOwnership.parentRow1931 := by rfl
theorem patch_mem0_2_0_8 : RadiusFivePruning.patch0_2_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1931, parentRow_mem1931, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1931_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_0_8]
  rfl
theorem row_eq0_2_0_9 : RadiusFivePruning.stateRow0_2_0_9 = ParentOwnership.parentRow0886 := by rfl
theorem patch_mem0_2_0_9 : RadiusFivePruning.patch0_2_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0886, parentRow_mem0886, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0886_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_0_9]
  rfl
theorem row_eq0_2_0_10 : RadiusFivePruning.stateRow0_2_0_10 = ParentOwnership.parentRow1944 := by rfl
theorem patch_mem0_2_0_10 : RadiusFivePruning.patch0_2_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1944, parentRow_mem1944, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1944_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_0_10]
  rfl
theorem row_eq0_2_0_11 : RadiusFivePruning.stateRow0_2_0_11 = ParentOwnership.parentRow1948 := by rfl
theorem patch_mem0_2_0_11 : RadiusFivePruning.patch0_2_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1948, parentRow_mem1948, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1948_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_0_11]
  rfl
theorem chunk_mem0_2_0 : ∀ p ∈ RadiusFivePruning.final0_2_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_2_0, List.forall_mem_cons]
  exact ⟨patch_mem0_2_0_0,⟨patch_mem0_2_0_1,⟨patch_mem0_2_0_3,⟨patch_mem0_2_0_4,⟨patch_mem0_2_0_5,⟨patch_mem0_2_0_6,⟨patch_mem0_2_0_8,⟨patch_mem0_2_0_9,⟨patch_mem0_2_0_10,⟨patch_mem0_2_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_2_1_0 : RadiusFivePruning.stateRow0_2_1_0 = ParentOwnership.parentRow1947 := by rfl
theorem patch_mem0_2_1_0 : RadiusFivePruning.patch0_2_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1947, parentRow_mem1947, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1947_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_1_0]
  rfl
theorem row_eq0_2_1_2 : RadiusFivePruning.stateRow0_2_1_2 = ParentOwnership.parentRow0689 := by rfl
theorem patch_mem0_2_1_2 : RadiusFivePruning.patch0_2_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0689, parentRow_mem0689, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0689_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_1_2]
  rfl
theorem row_eq0_2_1_4 : RadiusFivePruning.stateRow0_2_1_4 = ParentOwnership.parentRow0690 := by rfl
theorem patch_mem0_2_1_4 : RadiusFivePruning.patch0_2_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0690, parentRow_mem0690, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0690_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_1_4]
  rfl
theorem row_eq0_2_1_5 : RadiusFivePruning.stateRow0_2_1_5 = ParentOwnership.parentRow1337 := by rfl
theorem patch_mem0_2_1_5 : RadiusFivePruning.patch0_2_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1337, parentRow_mem1337, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1337_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_1_5]
  rfl
theorem row_eq0_2_1_6 : RadiusFivePruning.stateRow0_2_1_6 = ParentOwnership.parentRow1360 := by rfl
theorem patch_mem0_2_1_6 : RadiusFivePruning.patch0_2_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1360, parentRow_mem1360, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1360_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_1_6]
  rfl
theorem row_eq0_2_1_9 : RadiusFivePruning.stateRow0_2_1_9 = ParentOwnership.parentRow1361 := by rfl
theorem patch_mem0_2_1_9 : RadiusFivePruning.patch0_2_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1361, parentRow_mem1361, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1361_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_1_9]
  rfl
theorem row_eq0_2_1_11 : RadiusFivePruning.stateRow0_2_1_11 = ParentOwnership.parentRow1362 := by rfl
theorem patch_mem0_2_1_11 : RadiusFivePruning.patch0_2_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1362, parentRow_mem1362, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1362_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_1_11]
  rfl
theorem chunk_mem0_2_1 : ∀ p ∈ RadiusFivePruning.final0_2_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_2_1, List.forall_mem_cons]
  exact ⟨patch_mem0_2_1_0,⟨patch_mem0_2_1_2,⟨patch_mem0_2_1_4,⟨patch_mem0_2_1_5,⟨patch_mem0_2_1_6,⟨patch_mem0_2_1_9,⟨patch_mem0_2_1_11,by simp⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
