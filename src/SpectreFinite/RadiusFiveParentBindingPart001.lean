module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock0T0C4
public import SpectreFinite.RadiusFivePruningLiteralBlock0T1C0
public import SpectreFinite.RadiusFivePruningLiteralBlock0T1C1
public import SpectreFinite.RadiusFivePruningLiteralBlock0T1C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq0_0_4_0 : RadiusFivePruning.stateRow0_0_4_0 = ParentOwnership.parentRow1276 := by rfl
theorem patch_mem0_0_4_0 : RadiusFivePruning.patch0_0_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1276, parentRow_mem1276, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1276_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_0_4_0]
  rfl
theorem row_eq0_0_4_1 : RadiusFivePruning.stateRow0_0_4_1 = ParentOwnership.parentRow1277 := by rfl
theorem patch_mem0_0_4_1 : RadiusFivePruning.patch0_0_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1277, parentRow_mem1277, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1277_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_0_4_1]
  rfl
theorem row_eq0_0_4_2 : RadiusFivePruning.stateRow0_0_4_2 = ParentOwnership.parentRow1278 := by rfl
theorem patch_mem0_0_4_2 : RadiusFivePruning.patch0_0_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1278, parentRow_mem1278, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1278_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_0_4_2]
  rfl
theorem row_eq0_0_4_4 : RadiusFivePruning.stateRow0_0_4_4 = ParentOwnership.parentRow1279 := by rfl
theorem patch_mem0_0_4_4 : RadiusFivePruning.patch0_0_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1279, parentRow_mem1279, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1279_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_0_4_4]
  rfl
theorem row_eq0_0_4_6 : RadiusFivePruning.stateRow0_0_4_6 = ParentOwnership.parentRow1280 := by rfl
theorem patch_mem0_0_4_6 : RadiusFivePruning.patch0_0_4_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1280, parentRow_mem1280, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1280_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_0_4_6]
  rfl
theorem row_eq0_0_4_7 : RadiusFivePruning.stateRow0_0_4_7 = ParentOwnership.parentRow1281 := by rfl
theorem patch_mem0_0_4_7 : RadiusFivePruning.patch0_0_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1281, parentRow_mem1281, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1281_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_0_4_7]
  rfl
theorem row_eq0_0_4_8 : RadiusFivePruning.stateRow0_0_4_8 = ParentOwnership.parentRow1282 := by rfl
theorem patch_mem0_0_4_8 : RadiusFivePruning.patch0_0_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1282, parentRow_mem1282, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1282_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_0_4_8]
  rfl
theorem row_eq0_0_4_9 : RadiusFivePruning.stateRow0_0_4_9 = ParentOwnership.parentRow1283 := by rfl
theorem patch_mem0_0_4_9 : RadiusFivePruning.patch0_0_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1283, parentRow_mem1283, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1283_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_0_4_9]
  rfl
theorem row_eq0_0_4_10 : RadiusFivePruning.stateRow0_0_4_10 = ParentOwnership.parentRow1284 := by rfl
theorem patch_mem0_0_4_10 : RadiusFivePruning.patch0_0_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1284, parentRow_mem1284, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1284_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_0_4_10]
  rfl
theorem chunk_mem0_0_4 : ∀ p ∈ RadiusFivePruning.final0_0_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_0_4, List.forall_mem_cons]
  exact ⟨patch_mem0_0_4_0,⟨patch_mem0_0_4_1,⟨patch_mem0_0_4_2,⟨patch_mem0_0_4_4,⟨patch_mem0_0_4_6,⟨patch_mem0_0_4_7,⟨patch_mem0_0_4_8,⟨patch_mem0_0_4_9,⟨patch_mem0_0_4_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_1_0_0 : RadiusFivePruning.stateRow0_1_0_0 = ParentOwnership.parentRow1746 := by rfl
theorem patch_mem0_1_0_0 : RadiusFivePruning.patch0_1_0_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1746, parentRow_mem1746, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1746_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_0_0]
  rfl
theorem row_eq0_1_0_1 : RadiusFivePruning.stateRow0_1_0_1 = ParentOwnership.parentRow2064 := by rfl
theorem patch_mem0_1_0_1 : RadiusFivePruning.patch0_1_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2064, parentRow_mem2064, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2064_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_0_1]
  rfl
theorem row_eq0_1_0_3 : RadiusFivePruning.stateRow0_1_0_3 = ParentOwnership.parentRow2065 := by rfl
theorem patch_mem0_1_0_3 : RadiusFivePruning.patch0_1_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2065, parentRow_mem2065, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2065_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_0_3]
  rfl
theorem row_eq0_1_0_4 : RadiusFivePruning.stateRow0_1_0_4 = ParentOwnership.parentRow2066 := by rfl
theorem patch_mem0_1_0_4 : RadiusFivePruning.patch0_1_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2066, parentRow_mem2066, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2066_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_0_4]
  rfl
theorem row_eq0_1_0_5 : RadiusFivePruning.stateRow0_1_0_5 = ParentOwnership.parentRow2067 := by rfl
theorem patch_mem0_1_0_5 : RadiusFivePruning.patch0_1_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2067, parentRow_mem2067, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2067_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_0_5]
  rfl
theorem row_eq0_1_0_6 : RadiusFivePruning.stateRow0_1_0_6 = ParentOwnership.parentRow1727 := by rfl
theorem patch_mem0_1_0_6 : RadiusFivePruning.patch0_1_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1727, parentRow_mem1727, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1727_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_0_6]
  rfl
theorem row_eq0_1_0_8 : RadiusFivePruning.stateRow0_1_0_8 = ParentOwnership.parentRow2056 := by rfl
theorem patch_mem0_1_0_8 : RadiusFivePruning.patch0_1_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2056, parentRow_mem2056, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2056_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_0_8]
  rfl
theorem row_eq0_1_0_9 : RadiusFivePruning.stateRow0_1_0_9 = ParentOwnership.parentRow2055 := by rfl
theorem patch_mem0_1_0_9 : RadiusFivePruning.patch0_1_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2055, parentRow_mem2055, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2055_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_0_9]
  rfl
theorem row_eq0_1_0_10 : RadiusFivePruning.stateRow0_1_0_10 = ParentOwnership.parentRow2057 := by rfl
theorem patch_mem0_1_0_10 : RadiusFivePruning.patch0_1_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2057, parentRow_mem2057, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2057_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_0_10]
  rfl
theorem row_eq0_1_0_11 : RadiusFivePruning.stateRow0_1_0_11 = ParentOwnership.parentRow2058 := by rfl
theorem patch_mem0_1_0_11 : RadiusFivePruning.patch0_1_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2058, parentRow_mem2058, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2058_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_0_11]
  rfl
theorem chunk_mem0_1_0 : ∀ p ∈ RadiusFivePruning.final0_1_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_1_0, List.forall_mem_cons]
  exact ⟨patch_mem0_1_0_0,⟨patch_mem0_1_0_1,⟨patch_mem0_1_0_3,⟨patch_mem0_1_0_4,⟨patch_mem0_1_0_5,⟨patch_mem0_1_0_6,⟨patch_mem0_1_0_8,⟨patch_mem0_1_0_9,⟨patch_mem0_1_0_10,⟨patch_mem0_1_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_1_1_0 : RadiusFivePruning.stateRow0_1_1_0 = ParentOwnership.parentRow2059 := by rfl
theorem patch_mem0_1_1_0 : RadiusFivePruning.patch0_1_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2059, parentRow_mem2059, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2059_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_1_0]
  rfl
theorem row_eq0_1_1_2 : RadiusFivePruning.stateRow0_1_1_2 = ParentOwnership.parentRow0091 := by rfl
theorem patch_mem0_1_1_2 : RadiusFivePruning.patch0_1_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0091, parentRow_mem0091, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0091_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_1_2]
  rfl
theorem row_eq0_1_1_4 : RadiusFivePruning.stateRow0_1_1_4 = ParentOwnership.parentRow0509 := by rfl
theorem patch_mem0_1_1_4 : RadiusFivePruning.patch0_1_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0509, parentRow_mem0509, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0509_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_1_4]
  rfl
theorem row_eq0_1_1_5 : RadiusFivePruning.stateRow0_1_1_5 = ParentOwnership.parentRow0317 := by rfl
theorem patch_mem0_1_1_5 : RadiusFivePruning.patch0_1_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0317, parentRow_mem0317, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0317_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_1_5]
  rfl
theorem row_eq0_1_1_6 : RadiusFivePruning.stateRow0_1_1_6 = ParentOwnership.parentRow0319 := by rfl
theorem patch_mem0_1_1_6 : RadiusFivePruning.patch0_1_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0319, parentRow_mem0319, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0319_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_1_6]
  rfl
theorem row_eq0_1_1_9 : RadiusFivePruning.stateRow0_1_1_9 = ParentOwnership.parentRow0320 := by rfl
theorem patch_mem0_1_1_9 : RadiusFivePruning.patch0_1_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0320, parentRow_mem0320, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0320_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_1_9]
  rfl
theorem row_eq0_1_1_11 : RadiusFivePruning.stateRow0_1_1_11 = ParentOwnership.parentRow1086 := by rfl
theorem patch_mem0_1_1_11 : RadiusFivePruning.patch0_1_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1086, parentRow_mem1086, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1086_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_1_11]
  rfl
theorem chunk_mem0_1_1 : ∀ p ∈ RadiusFivePruning.final0_1_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_1_1, List.forall_mem_cons]
  exact ⟨patch_mem0_1_1_0,⟨patch_mem0_1_1_2,⟨patch_mem0_1_1_4,⟨patch_mem0_1_1_5,⟨patch_mem0_1_1_6,⟨patch_mem0_1_1_9,⟨patch_mem0_1_1_11,by simp⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_1_2_0 : RadiusFivePruning.stateRow0_1_2_0 = ParentOwnership.parentRow0513 := by rfl
theorem patch_mem0_1_2_0 : RadiusFivePruning.patch0_1_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0513, parentRow_mem0513, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0513_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_2_0]
  rfl
theorem row_eq0_1_2_1 : RadiusFivePruning.stateRow0_1_2_1 = ParentOwnership.parentRow0510 := by rfl
theorem patch_mem0_1_2_1 : RadiusFivePruning.patch0_1_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0510, parentRow_mem0510, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0510_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_2_1]
  rfl
theorem row_eq0_1_2_2 : RadiusFivePruning.stateRow0_1_2_2 = ParentOwnership.parentRow0511 := by rfl
theorem patch_mem0_1_2_2 : RadiusFivePruning.patch0_1_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0511, parentRow_mem0511, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0511_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_2_2]
  rfl
theorem row_eq0_1_2_3 : RadiusFivePruning.stateRow0_1_2_3 = ParentOwnership.parentRow0512 := by rfl
theorem patch_mem0_1_2_3 : RadiusFivePruning.patch0_1_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0512, parentRow_mem0512, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0512_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_2_3]
  rfl
theorem row_eq0_1_2_5 : RadiusFivePruning.stateRow0_1_2_5 = ParentOwnership.parentRow1679 := by rfl
theorem patch_mem0_1_2_5 : RadiusFivePruning.patch0_1_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1679, parentRow_mem1679, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1679_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_2_5]
  rfl
theorem row_eq0_1_2_6 : RadiusFivePruning.stateRow0_1_2_6 = ParentOwnership.parentRow1681 := by rfl
theorem patch_mem0_1_2_6 : RadiusFivePruning.patch0_1_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1681, parentRow_mem1681, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1681_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_2_6]
  rfl
theorem row_eq0_1_2_7 : RadiusFivePruning.stateRow0_1_2_7 = ParentOwnership.parentRow1676 := by rfl
theorem patch_mem0_1_2_7 : RadiusFivePruning.patch0_1_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1676, parentRow_mem1676, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1676_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_2_7]
  rfl
theorem row_eq0_1_2_8 : RadiusFivePruning.stateRow0_1_2_8 = ParentOwnership.parentRow1677 := by rfl
theorem patch_mem0_1_2_8 : RadiusFivePruning.patch0_1_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1677, parentRow_mem1677, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1677_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_2_8]
  rfl
theorem row_eq0_1_2_9 : RadiusFivePruning.stateRow0_1_2_9 = ParentOwnership.parentRow1678 := by rfl
theorem patch_mem0_1_2_9 : RadiusFivePruning.patch0_1_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1678, parentRow_mem1678, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1678_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_2_9]
  rfl
theorem row_eq0_1_2_10 : RadiusFivePruning.stateRow0_1_2_10 = ParentOwnership.parentRow1680 := by rfl
theorem patch_mem0_1_2_10 : RadiusFivePruning.patch0_1_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1680, parentRow_mem1680, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1680_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_1_2_10]
  rfl
theorem chunk_mem0_1_2 : ∀ p ∈ RadiusFivePruning.final0_1_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_1_2, List.forall_mem_cons]
  exact ⟨patch_mem0_1_2_0,⟨patch_mem0_1_2_1,⟨patch_mem0_1_2_2,⟨patch_mem0_1_2_3,⟨patch_mem0_1_2_5,⟨patch_mem0_1_2_6,⟨patch_mem0_1_2_7,⟨patch_mem0_1_2_8,⟨patch_mem0_1_2_9,⟨patch_mem0_1_2_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
