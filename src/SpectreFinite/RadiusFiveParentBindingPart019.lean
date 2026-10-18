module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock4T1C0
public import SpectreFinite.RadiusFivePruningLiteralBlock4T1C1
public import SpectreFinite.RadiusFivePruningLiteralBlock4T1C2
public import SpectreFinite.RadiusFivePruningLiteralBlock4T1C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq4_1_0_1 : RadiusFivePruning.stateRow4_1_0_1 = ParentOwnership.parentRow1956 := by rfl
theorem patch_mem4_1_0_1 : RadiusFivePruning.patch4_1_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1956, parentRow_mem1956, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1956_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_0_1]
  rfl
theorem row_eq4_1_0_3 : RadiusFivePruning.stateRow4_1_0_3 = ParentOwnership.parentRow1551 := by rfl
theorem patch_mem4_1_0_3 : RadiusFivePruning.patch4_1_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1551, parentRow_mem1551, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1551_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_0_3]
  rfl
theorem row_eq4_1_0_4 : RadiusFivePruning.stateRow4_1_0_4 = ParentOwnership.parentRow1559 := by rfl
theorem patch_mem4_1_0_4 : RadiusFivePruning.patch4_1_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1559, parentRow_mem1559, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1559_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_0_4]
  rfl
theorem row_eq4_1_0_6 : RadiusFivePruning.stateRow4_1_0_6 = ParentOwnership.parentRow1577 := by rfl
theorem patch_mem4_1_0_6 : RadiusFivePruning.patch4_1_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1577, parentRow_mem1577, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1577_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_0_6]
  rfl
theorem row_eq4_1_0_7 : RadiusFivePruning.stateRow4_1_0_7 = ParentOwnership.parentRow1578 := by rfl
theorem patch_mem4_1_0_7 : RadiusFivePruning.patch4_1_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1578, parentRow_mem1578, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1578_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_0_7]
  rfl
theorem row_eq4_1_0_9 : RadiusFivePruning.stateRow4_1_0_9 = ParentOwnership.parentRow1585 := by rfl
theorem patch_mem4_1_0_9 : RadiusFivePruning.patch4_1_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1585, parentRow_mem1585, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1585_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_0_9]
  rfl
theorem row_eq4_1_0_10 : RadiusFivePruning.stateRow4_1_0_10 = ParentOwnership.parentRow1586 := by rfl
theorem patch_mem4_1_0_10 : RadiusFivePruning.patch4_1_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1586, parentRow_mem1586, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1586_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_0_10]
  rfl
theorem row_eq4_1_0_11 : RadiusFivePruning.stateRow4_1_0_11 = ParentOwnership.parentRow1587 := by rfl
theorem patch_mem4_1_0_11 : RadiusFivePruning.patch4_1_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1587, parentRow_mem1587, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1587_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_0_11]
  rfl
theorem chunk_mem4_1_0 : ∀ p ∈ RadiusFivePruning.final4_1_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_1_0, List.forall_mem_cons]
  exact ⟨patch_mem4_1_0_1,⟨patch_mem4_1_0_3,⟨patch_mem4_1_0_4,⟨patch_mem4_1_0_6,⟨patch_mem4_1_0_7,⟨patch_mem4_1_0_9,⟨patch_mem4_1_0_10,⟨patch_mem4_1_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_1_1_0 : RadiusFivePruning.stateRow4_1_1_0 = ParentOwnership.parentRow1594 := by rfl
theorem patch_mem4_1_1_0 : RadiusFivePruning.patch4_1_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1594, parentRow_mem1594, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1594_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_1_0]
  rfl
theorem row_eq4_1_1_1 : RadiusFivePruning.stateRow4_1_1_1 = ParentOwnership.parentRow1595 := by rfl
theorem patch_mem4_1_1_1 : RadiusFivePruning.patch4_1_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1595, parentRow_mem1595, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1595_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_1_1]
  rfl
theorem row_eq4_1_1_3 : RadiusFivePruning.stateRow4_1_1_3 = ParentOwnership.parentRow1598 := by rfl
theorem patch_mem4_1_1_3 : RadiusFivePruning.patch4_1_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1598, parentRow_mem1598, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1598_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_1_3]
  rfl
theorem row_eq4_1_1_4 : RadiusFivePruning.stateRow4_1_1_4 = ParentOwnership.parentRow1600 := by rfl
theorem patch_mem4_1_1_4 : RadiusFivePruning.patch4_1_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1600, parentRow_mem1600, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1600_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_1_4]
  rfl
theorem row_eq4_1_1_5 : RadiusFivePruning.stateRow4_1_1_5 = ParentOwnership.parentRow1962 := by rfl
theorem patch_mem4_1_1_5 : RadiusFivePruning.patch4_1_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1962, parentRow_mem1962, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1962_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_1_5]
  rfl
theorem row_eq4_1_1_6 : RadiusFivePruning.stateRow4_1_1_6 = ParentOwnership.parentRow1560 := by rfl
theorem patch_mem4_1_1_6 : RadiusFivePruning.patch4_1_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1560, parentRow_mem1560, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1560_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_1_6]
  rfl
theorem row_eq4_1_1_7 : RadiusFivePruning.stateRow4_1_1_7 = ParentOwnership.parentRow1596 := by rfl
theorem patch_mem4_1_1_7 : RadiusFivePruning.patch4_1_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1596, parentRow_mem1596, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1596_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_1_7]
  rfl
theorem row_eq4_1_1_8 : RadiusFivePruning.stateRow4_1_1_8 = ParentOwnership.parentRow1597 := by rfl
theorem patch_mem4_1_1_8 : RadiusFivePruning.patch4_1_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1597, parentRow_mem1597, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1597_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_1_8]
  rfl
theorem row_eq4_1_1_10 : RadiusFivePruning.stateRow4_1_1_10 = ParentOwnership.parentRow1601 := by rfl
theorem patch_mem4_1_1_10 : RadiusFivePruning.patch4_1_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1601, parentRow_mem1601, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1601_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_1_10]
  rfl
theorem chunk_mem4_1_1 : ∀ p ∈ RadiusFivePruning.final4_1_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_1_1, List.forall_mem_cons]
  exact ⟨patch_mem4_1_1_0,⟨patch_mem4_1_1_1,⟨patch_mem4_1_1_3,⟨patch_mem4_1_1_4,⟨patch_mem4_1_1_5,⟨patch_mem4_1_1_6,⟨patch_mem4_1_1_7,⟨patch_mem4_1_1_8,⟨patch_mem4_1_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_1_2_0 : RadiusFivePruning.stateRow4_1_2_0 = ParentOwnership.parentRow0807 := by rfl
theorem patch_mem4_1_2_0 : RadiusFivePruning.patch4_1_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0807, parentRow_mem0807, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0807_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_2_0]
  rfl
theorem row_eq4_1_2_1 : RadiusFivePruning.stateRow4_1_2_1 = ParentOwnership.parentRow0815 := by rfl
theorem patch_mem4_1_2_1 : RadiusFivePruning.patch4_1_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0815, parentRow_mem0815, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0815_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_2_1]
  rfl
theorem row_eq4_1_2_2 : RadiusFivePruning.stateRow4_1_2_2 = ParentOwnership.parentRow0816 := by rfl
theorem patch_mem4_1_2_2 : RadiusFivePruning.patch4_1_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0816, parentRow_mem0816, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0816_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_2_2]
  rfl
theorem row_eq4_1_2_4 : RadiusFivePruning.stateRow4_1_2_4 = ParentOwnership.parentRow0811 := by rfl
theorem patch_mem4_1_2_4 : RadiusFivePruning.patch4_1_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0811, parentRow_mem0811, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0811_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_2_4]
  rfl
theorem row_eq4_1_2_6 : RadiusFivePruning.stateRow4_1_2_6 = ParentOwnership.parentRow1552 := by rfl
theorem patch_mem4_1_2_6 : RadiusFivePruning.patch4_1_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1552, parentRow_mem1552, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1552_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_2_6]
  rfl
theorem row_eq4_1_2_7 : RadiusFivePruning.stateRow4_1_2_7 = ParentOwnership.parentRow1571 := by rfl
theorem patch_mem4_1_2_7 : RadiusFivePruning.patch4_1_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1571, parentRow_mem1571, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1571_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_2_7]
  rfl
theorem row_eq4_1_2_9 : RadiusFivePruning.stateRow4_1_2_9 = ParentOwnership.parentRow1593 := by rfl
theorem patch_mem4_1_2_9 : RadiusFivePruning.patch4_1_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1593, parentRow_mem1593, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1593_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_2_9]
  rfl
theorem row_eq4_1_2_10 : RadiusFivePruning.stateRow4_1_2_10 = ParentOwnership.parentRow1581 := by rfl
theorem patch_mem4_1_2_10 : RadiusFivePruning.patch4_1_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1581, parentRow_mem1581, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1581_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_2_10]
  rfl
theorem row_eq4_1_2_11 : RadiusFivePruning.stateRow4_1_2_11 = ParentOwnership.parentRow1582 := by rfl
theorem patch_mem4_1_2_11 : RadiusFivePruning.patch4_1_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1582, parentRow_mem1582, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1582_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_2_11]
  rfl
theorem chunk_mem4_1_2 : ∀ p ∈ RadiusFivePruning.final4_1_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_1_2, List.forall_mem_cons]
  exact ⟨patch_mem4_1_2_0,⟨patch_mem4_1_2_1,⟨patch_mem4_1_2_2,⟨patch_mem4_1_2_4,⟨patch_mem4_1_2_6,⟨patch_mem4_1_2_7,⟨patch_mem4_1_2_9,⟨patch_mem4_1_2_10,⟨patch_mem4_1_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_1_3_0 : RadiusFivePruning.stateRow4_1_3_0 = ParentOwnership.parentRow1591 := by rfl
theorem patch_mem4_1_3_0 : RadiusFivePruning.patch4_1_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1591, parentRow_mem1591, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1591_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_3_0]
  rfl
theorem row_eq4_1_3_1 : RadiusFivePruning.stateRow4_1_3_1 = ParentOwnership.parentRow1592 := by rfl
theorem patch_mem4_1_3_1 : RadiusFivePruning.patch4_1_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1592, parentRow_mem1592, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1592_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_3_1]
  rfl
theorem row_eq4_1_3_2 : RadiusFivePruning.stateRow4_1_3_2 = ParentOwnership.parentRow1525 := by rfl
theorem patch_mem4_1_3_2 : RadiusFivePruning.patch4_1_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1525, parentRow_mem1525, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1525_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_3_2]
  rfl
theorem row_eq4_1_3_3 : RadiusFivePruning.stateRow4_1_3_3 = ParentOwnership.parentRow1553 := by rfl
theorem patch_mem4_1_3_3 : RadiusFivePruning.patch4_1_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1553, parentRow_mem1553, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1553_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_3_3]
  rfl
theorem row_eq4_1_3_4 : RadiusFivePruning.stateRow4_1_3_4 = ParentOwnership.parentRow1572 := by rfl
theorem patch_mem4_1_3_4 : RadiusFivePruning.patch4_1_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1572, parentRow_mem1572, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1572_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_3_4]
  rfl
theorem row_eq4_1_3_6 : RadiusFivePruning.stateRow4_1_3_6 = ParentOwnership.parentRow1583 := by rfl
theorem patch_mem4_1_3_6 : RadiusFivePruning.patch4_1_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1583, parentRow_mem1583, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1583_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_3_6]
  rfl
theorem row_eq4_1_3_7 : RadiusFivePruning.stateRow4_1_3_7 = ParentOwnership.parentRow1584 := by rfl
theorem patch_mem4_1_3_7 : RadiusFivePruning.patch4_1_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1584, parentRow_mem1584, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1584_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_3_7]
  rfl
theorem row_eq4_1_3_9 : RadiusFivePruning.stateRow4_1_3_9 = ParentOwnership.parentRow1526 := by rfl
theorem patch_mem4_1_3_9 : RadiusFivePruning.patch4_1_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1526, parentRow_mem1526, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1526_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_1_3_9]
  rfl
theorem chunk_mem4_1_3 : ∀ p ∈ RadiusFivePruning.final4_1_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_1_3, List.forall_mem_cons]
  exact ⟨patch_mem4_1_3_0,⟨patch_mem4_1_3_1,⟨patch_mem4_1_3_2,⟨patch_mem4_1_3_3,⟨patch_mem4_1_3_4,⟨patch_mem4_1_3_6,⟨patch_mem4_1_3_7,⟨patch_mem4_1_3_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
