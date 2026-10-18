module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock5T0C0
public import SpectreFinite.RadiusFivePruningLiteralBlock5T0C1
public import SpectreFinite.RadiusFivePruningLiteralBlock5T0C2
public import SpectreFinite.RadiusFivePruningLiteralBlock5T1C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq5_0_0_2 : RadiusFivePruning.stateRow5_0_0_2 = ParentOwnership.parentRow1646 := by rfl
theorem patch_mem5_0_0_2 : RadiusFivePruning.patch5_0_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1646, parentRow_mem1646, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1646_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_0_2]
  rfl
theorem row_eq5_0_0_3 : RadiusFivePruning.stateRow5_0_0_3 = ParentOwnership.parentRow1664 := by rfl
theorem patch_mem5_0_0_3 : RadiusFivePruning.patch5_0_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1664, parentRow_mem1664, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1664_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_0_3]
  rfl
theorem row_eq5_0_0_4 : RadiusFivePruning.stateRow5_0_0_4 = ParentOwnership.parentRow0051 := by rfl
theorem patch_mem5_0_0_4 : RadiusFivePruning.patch5_0_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0051, parentRow_mem0051, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0051_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_0_4]
  rfl
theorem row_eq5_0_0_6 : RadiusFivePruning.stateRow5_0_0_6 = ParentOwnership.parentRow0491 := by rfl
theorem patch_mem5_0_0_6 : RadiusFivePruning.patch5_0_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0491, parentRow_mem0491, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0491_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_0_6]
  rfl
theorem row_eq5_0_0_7 : RadiusFivePruning.stateRow5_0_0_7 = ParentOwnership.parentRow0495 := by rfl
theorem patch_mem5_0_0_7 : RadiusFivePruning.patch5_0_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0495, parentRow_mem0495, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0495_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_0_7]
  rfl
theorem row_eq5_0_0_9 : RadiusFivePruning.stateRow5_0_0_9 = ParentOwnership.parentRow1613 := by rfl
theorem patch_mem5_0_0_9 : RadiusFivePruning.patch5_0_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1613, parentRow_mem1613, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1613_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_0_9]
  rfl
theorem row_eq5_0_0_10 : RadiusFivePruning.stateRow5_0_0_10 = ParentOwnership.parentRow1614 := by rfl
theorem patch_mem5_0_0_10 : RadiusFivePruning.patch5_0_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1614, parentRow_mem1614, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1614_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_0_10]
  rfl
theorem row_eq5_0_0_11 : RadiusFivePruning.stateRow5_0_0_11 = ParentOwnership.parentRow1615 := by rfl
theorem patch_mem5_0_0_11 : RadiusFivePruning.patch5_0_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1615, parentRow_mem1615, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1615_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_0_11]
  rfl
theorem chunk_mem5_0_0 : ∀ p ∈ RadiusFivePruning.final5_0_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_0_0, List.forall_mem_cons]
  exact ⟨patch_mem5_0_0_2,⟨patch_mem5_0_0_3,⟨patch_mem5_0_0_4,⟨patch_mem5_0_0_6,⟨patch_mem5_0_0_7,⟨patch_mem5_0_0_9,⟨patch_mem5_0_0_10,⟨patch_mem5_0_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq5_0_1_0 : RadiusFivePruning.stateRow5_0_1_0 = ParentOwnership.parentRow1616 := by rfl
theorem patch_mem5_0_1_0 : RadiusFivePruning.patch5_0_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1616, parentRow_mem1616, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1616_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_1_0]
  rfl
theorem row_eq5_0_1_1 : RadiusFivePruning.stateRow5_0_1_1 = ParentOwnership.parentRow1617 := by rfl
theorem patch_mem5_0_1_1 : RadiusFivePruning.patch5_0_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1617, parentRow_mem1617, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1617_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_1_1]
  rfl
theorem row_eq5_0_1_3 : RadiusFivePruning.stateRow5_0_1_3 = ParentOwnership.parentRow1618 := by rfl
theorem patch_mem5_0_1_3 : RadiusFivePruning.patch5_0_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1618, parentRow_mem1618, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1618_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_1_3]
  rfl
theorem row_eq5_0_1_4 : RadiusFivePruning.stateRow5_0_1_4 = ParentOwnership.parentRow1619 := by rfl
theorem patch_mem5_0_1_4 : RadiusFivePruning.patch5_0_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1619, parentRow_mem1619, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1619_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_1_4]
  rfl
theorem row_eq5_0_1_7 : RadiusFivePruning.stateRow5_0_1_7 = ParentOwnership.parentRow1620 := by rfl
theorem patch_mem5_0_1_7 : RadiusFivePruning.patch5_0_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1620, parentRow_mem1620, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1620_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_1_7]
  rfl
theorem row_eq5_0_1_8 : RadiusFivePruning.stateRow5_0_1_8 = ParentOwnership.parentRow1621 := by rfl
theorem patch_mem5_0_1_8 : RadiusFivePruning.patch5_0_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1621, parentRow_mem1621, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1621_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_1_8]
  rfl
theorem row_eq5_0_1_9 : RadiusFivePruning.stateRow5_0_1_9 = ParentOwnership.parentRow1622 := by rfl
theorem patch_mem5_0_1_9 : RadiusFivePruning.patch5_0_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1622, parentRow_mem1622, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1622_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_1_9]
  rfl
theorem row_eq5_0_1_11 : RadiusFivePruning.stateRow5_0_1_11 = ParentOwnership.parentRow1623 := by rfl
theorem patch_mem5_0_1_11 : RadiusFivePruning.patch5_0_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1623, parentRow_mem1623, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1623_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_1_11]
  rfl
theorem chunk_mem5_0_1 : ∀ p ∈ RadiusFivePruning.final5_0_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_0_1, List.forall_mem_cons]
  exact ⟨patch_mem5_0_1_0,⟨patch_mem5_0_1_1,⟨patch_mem5_0_1_3,⟨patch_mem5_0_1_4,⟨patch_mem5_0_1_7,⟨patch_mem5_0_1_8,⟨patch_mem5_0_1_9,⟨patch_mem5_0_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq5_0_2_0 : RadiusFivePruning.stateRow5_0_2_0 = ParentOwnership.parentRow1624 := by rfl
theorem patch_mem5_0_2_0 : RadiusFivePruning.patch5_0_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1624, parentRow_mem1624, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1624_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_2_0]
  rfl
theorem row_eq5_0_2_1 : RadiusFivePruning.stateRow5_0_2_1 = ParentOwnership.parentRow1625 := by rfl
theorem patch_mem5_0_2_1 : RadiusFivePruning.patch5_0_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1625, parentRow_mem1625, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1625_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_2_1]
  rfl
theorem row_eq5_0_2_2 : RadiusFivePruning.stateRow5_0_2_2 = ParentOwnership.parentRow1642 := by rfl
theorem patch_mem5_0_2_2 : RadiusFivePruning.patch5_0_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1642, parentRow_mem1642, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1642_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_2_2]
  rfl
theorem row_eq5_0_2_3 : RadiusFivePruning.stateRow5_0_2_3 = ParentOwnership.parentRow1643 := by rfl
theorem patch_mem5_0_2_3 : RadiusFivePruning.patch5_0_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1643, parentRow_mem1643, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1643_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_2_3]
  rfl
theorem row_eq5_0_2_4 : RadiusFivePruning.stateRow5_0_2_4 = ParentOwnership.parentRow1644 := by rfl
theorem patch_mem5_0_2_4 : RadiusFivePruning.patch5_0_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1644, parentRow_mem1644, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1644_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_2_4]
  rfl
theorem row_eq5_0_2_5 : RadiusFivePruning.stateRow5_0_2_5 = ParentOwnership.parentRow1645 := by rfl
theorem patch_mem5_0_2_5 : RadiusFivePruning.patch5_0_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1645, parentRow_mem1645, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1645_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_2_5]
  rfl
theorem row_eq5_0_2_6 : RadiusFivePruning.stateRow5_0_2_6 = ParentOwnership.parentRow1647 := by rfl
theorem patch_mem5_0_2_6 : RadiusFivePruning.patch5_0_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1647, parentRow_mem1647, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1647_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_2_6]
  rfl
theorem row_eq5_0_2_7 : RadiusFivePruning.stateRow5_0_2_7 = ParentOwnership.parentRow1648 := by rfl
theorem patch_mem5_0_2_7 : RadiusFivePruning.patch5_0_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1648, parentRow_mem1648, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1648_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_2_7]
  rfl
theorem row_eq5_0_2_8 : RadiusFivePruning.stateRow5_0_2_8 = ParentOwnership.parentRow1649 := by rfl
theorem patch_mem5_0_2_8 : RadiusFivePruning.patch5_0_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1649, parentRow_mem1649, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1649_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_2_8]
  rfl
theorem row_eq5_0_2_9 : RadiusFivePruning.stateRow5_0_2_9 = ParentOwnership.parentRow1650 := by rfl
theorem patch_mem5_0_2_9 : RadiusFivePruning.patch5_0_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1650, parentRow_mem1650, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1650_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_2_9]
  rfl
theorem row_eq5_0_2_10 : RadiusFivePruning.stateRow5_0_2_10 = ParentOwnership.parentRow2001 := by rfl
theorem patch_mem5_0_2_10 : RadiusFivePruning.patch5_0_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2001, parentRow_mem2001, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2001_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_0_2_10]
  rfl
theorem chunk_mem5_0_2 : ∀ p ∈ RadiusFivePruning.final5_0_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_0_2, List.forall_mem_cons]
  exact ⟨patch_mem5_0_2_0,⟨patch_mem5_0_2_1,⟨patch_mem5_0_2_2,⟨patch_mem5_0_2_3,⟨patch_mem5_0_2_4,⟨patch_mem5_0_2_5,⟨patch_mem5_0_2_6,⟨patch_mem5_0_2_7,⟨patch_mem5_0_2_8,⟨patch_mem5_0_2_9,⟨patch_mem5_0_2_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq5_1_0_2 : RadiusFivePruning.stateRow5_1_0_2 = ParentOwnership.parentRow0725 := by rfl
theorem patch_mem5_1_0_2 : RadiusFivePruning.patch5_1_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0725, parentRow_mem0725, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0725_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_0_2]
  rfl
theorem row_eq5_1_0_3 : RadiusFivePruning.stateRow5_1_0_3 = ParentOwnership.parentRow0570 := by rfl
theorem patch_mem5_1_0_3 : RadiusFivePruning.patch5_1_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0570, parentRow_mem0570, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0570_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_0_3]
  rfl
theorem row_eq5_1_0_4 : RadiusFivePruning.stateRow5_1_0_4 = ParentOwnership.parentRow0802 := by rfl
theorem patch_mem5_1_0_4 : RadiusFivePruning.patch5_1_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0802, parentRow_mem0802, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0802_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_0_4]
  rfl
theorem row_eq5_1_0_6 : RadiusFivePruning.stateRow5_1_0_6 = ParentOwnership.parentRow0583 := by rfl
theorem patch_mem5_1_0_6 : RadiusFivePruning.patch5_1_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0583, parentRow_mem0583, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0583_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_0_6]
  rfl
theorem row_eq5_1_0_7 : RadiusFivePruning.stateRow5_1_0_7 = ParentOwnership.parentRow0800 := by rfl
theorem patch_mem5_1_0_7 : RadiusFivePruning.patch5_1_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0800, parentRow_mem0800, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0800_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_0_7]
  rfl
theorem row_eq5_1_0_9 : RadiusFivePruning.stateRow5_1_0_9 = ParentOwnership.parentRow1414 := by rfl
theorem patch_mem5_1_0_9 : RadiusFivePruning.patch5_1_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1414, parentRow_mem1414, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1414_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_0_9]
  rfl
theorem row_eq5_1_0_10 : RadiusFivePruning.stateRow5_1_0_10 = ParentOwnership.parentRow1416 := by rfl
theorem patch_mem5_1_0_10 : RadiusFivePruning.patch5_1_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1416, parentRow_mem1416, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1416_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_0_10]
  rfl
theorem row_eq5_1_0_11 : RadiusFivePruning.stateRow5_1_0_11 = ParentOwnership.parentRow1415 := by rfl
theorem patch_mem5_1_0_11 : RadiusFivePruning.patch5_1_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1415, parentRow_mem1415, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1415_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_0_11]
  rfl
theorem chunk_mem5_1_0 : ∀ p ∈ RadiusFivePruning.final5_1_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_1_0, List.forall_mem_cons]
  exact ⟨patch_mem5_1_0_2,⟨patch_mem5_1_0_3,⟨patch_mem5_1_0_4,⟨patch_mem5_1_0_6,⟨patch_mem5_1_0_7,⟨patch_mem5_1_0_9,⟨patch_mem5_1_0_10,⟨patch_mem5_1_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
