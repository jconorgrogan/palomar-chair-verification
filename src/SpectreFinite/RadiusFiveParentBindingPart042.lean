module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock7T2C0
public import SpectreFinite.RadiusFivePruningLiteralBlock7T2C1
public import SpectreFinite.RadiusFivePruningLiteralBlock7T2C2
public import SpectreFinite.RadiusFivePruningLiteralBlock7T2C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq7_2_0_1 : RadiusFivePruning.stateRow7_2_0_1 = ParentOwnership.parentRow0187 := by rfl
theorem patch_mem7_2_0_1 : RadiusFivePruning.patch7_2_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0187, parentRow_mem0187, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0187_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_0_1]
  rfl
theorem row_eq7_2_0_2 : RadiusFivePruning.stateRow7_2_0_2 = ParentOwnership.parentRow1411 := by rfl
theorem patch_mem7_2_0_2 : RadiusFivePruning.patch7_2_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1411, parentRow_mem1411, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1411_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_0_2]
  rfl
theorem row_eq7_2_0_3 : RadiusFivePruning.stateRow7_2_0_3 = ParentOwnership.parentRow1413 := by rfl
theorem patch_mem7_2_0_3 : RadiusFivePruning.patch7_2_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1413, parentRow_mem1413, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1413_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_0_3]
  rfl
theorem row_eq7_2_0_4 : RadiusFivePruning.stateRow7_2_0_4 = ParentOwnership.parentRow0330 := by rfl
theorem patch_mem7_2_0_4 : RadiusFivePruning.patch7_2_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0330, parentRow_mem0330, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0330_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_0_4]
  rfl
theorem row_eq7_2_0_5 : RadiusFivePruning.stateRow7_2_0_5 = ParentOwnership.parentRow0332 := by rfl
theorem patch_mem7_2_0_5 : RadiusFivePruning.patch7_2_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0332, parentRow_mem0332, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0332_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_0_5]
  rfl
theorem row_eq7_2_0_6 : RadiusFivePruning.stateRow7_2_0_6 = ParentOwnership.parentRow1432 := by rfl
theorem patch_mem7_2_0_6 : RadiusFivePruning.patch7_2_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1432, parentRow_mem1432, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1432_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_0_6]
  rfl
theorem row_eq7_2_0_7 : RadiusFivePruning.stateRow7_2_0_7 = ParentOwnership.parentRow1434 := by rfl
theorem patch_mem7_2_0_7 : RadiusFivePruning.patch7_2_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1434, parentRow_mem1434, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1434_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_0_7]
  rfl
theorem row_eq7_2_0_8 : RadiusFivePruning.stateRow7_2_0_8 = ParentOwnership.parentRow1387 := by rfl
theorem patch_mem7_2_0_8 : RadiusFivePruning.patch7_2_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1387, parentRow_mem1387, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1387_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_0_8]
  rfl
theorem row_eq7_2_0_11 : RadiusFivePruning.stateRow7_2_0_11 = ParentOwnership.parentRow0183 := by rfl
theorem patch_mem7_2_0_11 : RadiusFivePruning.patch7_2_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0183, parentRow_mem0183, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0183_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_0_11]
  rfl
theorem chunk_mem7_2_0 : ∀ p ∈ RadiusFivePruning.final7_2_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_2_0, List.forall_mem_cons]
  exact ⟨patch_mem7_2_0_1,⟨patch_mem7_2_0_2,⟨patch_mem7_2_0_3,⟨patch_mem7_2_0_4,⟨patch_mem7_2_0_5,⟨patch_mem7_2_0_6,⟨patch_mem7_2_0_7,⟨patch_mem7_2_0_8,⟨patch_mem7_2_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_2_1_0 : RadiusFivePruning.stateRow7_2_1_0 = ParentOwnership.parentRow0322 := by rfl
theorem patch_mem7_2_1_0 : RadiusFivePruning.patch7_2_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0322, parentRow_mem0322, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0322_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_1_0]
  rfl
theorem row_eq7_2_1_2 : RadiusFivePruning.stateRow7_2_1_2 = ParentOwnership.parentRow1388 := by rfl
theorem patch_mem7_2_1_2 : RadiusFivePruning.patch7_2_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1388, parentRow_mem1388, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1388_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_1_2]
  rfl
theorem row_eq7_2_1_3 : RadiusFivePruning.stateRow7_2_1_3 = ParentOwnership.parentRow1399 := by rfl
theorem patch_mem7_2_1_3 : RadiusFivePruning.patch7_2_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1399, parentRow_mem1399, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1399_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_1_3]
  rfl
theorem row_eq7_2_1_4 : RadiusFivePruning.stateRow7_2_1_4 = ParentOwnership.parentRow1389 := by rfl
theorem patch_mem7_2_1_4 : RadiusFivePruning.patch7_2_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1389, parentRow_mem1389, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1389_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_1_4]
  rfl
theorem row_eq7_2_1_5 : RadiusFivePruning.stateRow7_2_1_5 = ParentOwnership.parentRow1400 := by rfl
theorem patch_mem7_2_1_5 : RadiusFivePruning.patch7_2_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1400, parentRow_mem1400, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1400_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_1_5]
  rfl
theorem row_eq7_2_1_6 : RadiusFivePruning.stateRow7_2_1_6 = ParentOwnership.parentRow1391 := by rfl
theorem patch_mem7_2_1_6 : RadiusFivePruning.patch7_2_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1391, parentRow_mem1391, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1391_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_1_6]
  rfl
theorem row_eq7_2_1_9 : RadiusFivePruning.stateRow7_2_1_9 = ParentOwnership.parentRow1392 := by rfl
theorem patch_mem7_2_1_9 : RadiusFivePruning.patch7_2_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1392, parentRow_mem1392, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1392_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_1_9]
  rfl
theorem row_eq7_2_1_10 : RadiusFivePruning.stateRow7_2_1_10 = ParentOwnership.parentRow1401 := by rfl
theorem patch_mem7_2_1_10 : RadiusFivePruning.patch7_2_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1401, parentRow_mem1401, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1401_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_1_10]
  rfl
theorem row_eq7_2_1_11 : RadiusFivePruning.stateRow7_2_1_11 = ParentOwnership.parentRow0323 := by rfl
theorem patch_mem7_2_1_11 : RadiusFivePruning.patch7_2_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0323, parentRow_mem0323, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0323_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_1_11]
  rfl
theorem chunk_mem7_2_1 : ∀ p ∈ RadiusFivePruning.final7_2_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_2_1, List.forall_mem_cons]
  exact ⟨patch_mem7_2_1_0,⟨patch_mem7_2_1_2,⟨patch_mem7_2_1_3,⟨patch_mem7_2_1_4,⟨patch_mem7_2_1_5,⟨patch_mem7_2_1_6,⟨patch_mem7_2_1_9,⟨patch_mem7_2_1_10,⟨patch_mem7_2_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_2_2_0 : RadiusFivePruning.stateRow7_2_2_0 = ParentOwnership.parentRow0590 := by rfl
theorem patch_mem7_2_2_0 : RadiusFivePruning.patch7_2_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0590, parentRow_mem0590, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0590_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_2_0]
  rfl
theorem row_eq7_2_2_1 : RadiusFivePruning.stateRow7_2_2_1 = ParentOwnership.parentRow1393 := by rfl
theorem patch_mem7_2_2_1 : RadiusFivePruning.patch7_2_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1393, parentRow_mem1393, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1393_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_2_1]
  rfl
theorem row_eq7_2_2_2 : RadiusFivePruning.stateRow7_2_2_2 = ParentOwnership.parentRow1403 := by rfl
theorem patch_mem7_2_2_2 : RadiusFivePruning.patch7_2_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1403, parentRow_mem1403, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1403_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_2_2]
  rfl
theorem row_eq7_2_2_3 : RadiusFivePruning.stateRow7_2_2_3 = ParentOwnership.parentRow1402 := by rfl
theorem patch_mem7_2_2_3 : RadiusFivePruning.patch7_2_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1402, parentRow_mem1402, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1402_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_2_3]
  rfl
theorem row_eq7_2_2_4 : RadiusFivePruning.stateRow7_2_2_4 = ParentOwnership.parentRow0325 := by rfl
theorem patch_mem7_2_2_4 : RadiusFivePruning.patch7_2_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0325, parentRow_mem0325, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0325_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_2_4]
  rfl
theorem row_eq7_2_2_5 : RadiusFivePruning.stateRow7_2_2_5 = ParentOwnership.parentRow0592 := by rfl
theorem patch_mem7_2_2_5 : RadiusFivePruning.patch7_2_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0592, parentRow_mem0592, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0592_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_2_5]
  rfl
theorem row_eq7_2_2_6 : RadiusFivePruning.stateRow7_2_2_6 = ParentOwnership.parentRow1404 := by rfl
theorem patch_mem7_2_2_6 : RadiusFivePruning.patch7_2_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1404, parentRow_mem1404, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1404_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_2_6]
  rfl
theorem row_eq7_2_2_8 : RadiusFivePruning.stateRow7_2_2_8 = ParentOwnership.parentRow1409 := by rfl
theorem patch_mem7_2_2_8 : RadiusFivePruning.patch7_2_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1409, parentRow_mem1409, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1409_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_2_8]
  rfl
theorem row_eq7_2_2_10 : RadiusFivePruning.stateRow7_2_2_10 = ParentOwnership.parentRow1410 := by rfl
theorem patch_mem7_2_2_10 : RadiusFivePruning.patch7_2_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1410, parentRow_mem1410, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1410_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_2_10]
  rfl
theorem row_eq7_2_2_11 : RadiusFivePruning.stateRow7_2_2_11 = ParentOwnership.parentRow1412 := by rfl
theorem patch_mem7_2_2_11 : RadiusFivePruning.patch7_2_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1412, parentRow_mem1412, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1412_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_2_11]
  rfl
theorem chunk_mem7_2_2 : ∀ p ∈ RadiusFivePruning.final7_2_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_2_2, List.forall_mem_cons]
  exact ⟨patch_mem7_2_2_0,⟨patch_mem7_2_2_1,⟨patch_mem7_2_2_2,⟨patch_mem7_2_2_3,⟨patch_mem7_2_2_4,⟨patch_mem7_2_2_5,⟨patch_mem7_2_2_6,⟨patch_mem7_2_2_8,⟨patch_mem7_2_2_10,⟨patch_mem7_2_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_2_3_0 : RadiusFivePruning.stateRow7_2_3_0 = ParentOwnership.parentRow0329 := by rfl
theorem patch_mem7_2_3_0 : RadiusFivePruning.patch7_2_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0329, parentRow_mem0329, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0329_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_3_0]
  rfl
theorem row_eq7_2_3_1 : RadiusFivePruning.stateRow7_2_3_1 = ParentOwnership.parentRow0331 := by rfl
theorem patch_mem7_2_3_1 : RadiusFivePruning.patch7_2_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0331, parentRow_mem0331, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0331_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_3_1]
  rfl
theorem row_eq7_2_3_2 : RadiusFivePruning.stateRow7_2_3_2 = ParentOwnership.parentRow1431 := by rfl
theorem patch_mem7_2_3_2 : RadiusFivePruning.patch7_2_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1431, parentRow_mem1431, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1431_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_3_2]
  rfl
theorem row_eq7_2_3_3 : RadiusFivePruning.stateRow7_2_3_3 = ParentOwnership.parentRow1433 := by rfl
theorem patch_mem7_2_3_3 : RadiusFivePruning.patch7_2_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1433, parentRow_mem1433, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1433_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_3_3]
  rfl
theorem row_eq7_2_3_5 : RadiusFivePruning.stateRow7_2_3_5 = ParentOwnership.parentRow1440 := by rfl
theorem patch_mem7_2_3_5 : RadiusFivePruning.patch7_2_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1440, parentRow_mem1440, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1440_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_3_5]
  rfl
theorem row_eq7_2_3_6 : RadiusFivePruning.stateRow7_2_3_6 = ParentOwnership.parentRow1446 := by rfl
theorem patch_mem7_2_3_6 : RadiusFivePruning.patch7_2_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1446, parentRow_mem1446, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1446_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_3_6]
  rfl
theorem row_eq7_2_3_7 : RadiusFivePruning.stateRow7_2_3_7 = ParentOwnership.parentRow0327 := by rfl
theorem patch_mem7_2_3_7 : RadiusFivePruning.patch7_2_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0327, parentRow_mem0327, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0327_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_3_7]
  rfl
theorem row_eq7_2_3_8 : RadiusFivePruning.stateRow7_2_3_8 = ParentOwnership.parentRow1429 := by rfl
theorem patch_mem7_2_3_8 : RadiusFivePruning.patch7_2_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1429, parentRow_mem1429, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1429_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_3_8]
  rfl
theorem row_eq7_2_3_9 : RadiusFivePruning.stateRow7_2_3_9 = ParentOwnership.parentRow1439 := by rfl
theorem patch_mem7_2_3_9 : RadiusFivePruning.patch7_2_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1439, parentRow_mem1439, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1439_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_3_9]
  rfl
theorem row_eq7_2_3_10 : RadiusFivePruning.stateRow7_2_3_10 = ParentOwnership.parentRow1445 := by rfl
theorem patch_mem7_2_3_10 : RadiusFivePruning.patch7_2_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1445, parentRow_mem1445, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1445_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_3_10]
  rfl
theorem row_eq7_2_3_11 : RadiusFivePruning.stateRow7_2_3_11 = ParentOwnership.parentRow1441 := by rfl
theorem patch_mem7_2_3_11 : RadiusFivePruning.patch7_2_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1441, parentRow_mem1441, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1441_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_2_3_11]
  rfl
theorem chunk_mem7_2_3 : ∀ p ∈ RadiusFivePruning.final7_2_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_2_3, List.forall_mem_cons]
  exact ⟨patch_mem7_2_3_0,⟨patch_mem7_2_3_1,⟨patch_mem7_2_3_2,⟨patch_mem7_2_3_3,⟨patch_mem7_2_3_5,⟨patch_mem7_2_3_6,⟨patch_mem7_2_3_7,⟨patch_mem7_2_3_8,⟨patch_mem7_2_3_9,⟨patch_mem7_2_3_10,⟨patch_mem7_2_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
