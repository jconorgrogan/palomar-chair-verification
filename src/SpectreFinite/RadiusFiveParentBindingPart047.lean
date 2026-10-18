module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock7T4C2
public import SpectreFinite.RadiusFivePruningLiteralBlock7T4C3
public import SpectreFinite.RadiusFivePruningLiteralBlock7T4C4
public import SpectreFinite.RadiusFivePruningLiteralBlock7T4C5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq7_4_2_0 : RadiusFivePruning.stateRow7_4_2_0 = ParentOwnership.parentRow1863 := by rfl
theorem patch_mem7_4_2_0 : RadiusFivePruning.patch7_4_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1863, parentRow_mem1863, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1863_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_2_0]
  rfl
theorem row_eq7_4_2_1 : RadiusFivePruning.stateRow7_4_2_1 = ParentOwnership.parentRow0859 := by rfl
theorem patch_mem7_4_2_1 : RadiusFivePruning.patch7_4_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0859, parentRow_mem0859, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0859_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_2_1]
  rfl
theorem row_eq7_4_2_2 : RadiusFivePruning.stateRow7_4_2_2 = ParentOwnership.parentRow0855 := by rfl
theorem patch_mem7_4_2_2 : RadiusFivePruning.patch7_4_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0855, parentRow_mem0855, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0855_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_2_2]
  rfl
theorem row_eq7_4_2_3 : RadiusFivePruning.stateRow7_4_2_3 = ParentOwnership.parentRow0971 := by rfl
theorem patch_mem7_4_2_3 : RadiusFivePruning.patch7_4_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0971, parentRow_mem0971, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0971_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_2_3]
  rfl
theorem row_eq7_4_2_4 : RadiusFivePruning.stateRow7_4_2_4 = ParentOwnership.parentRow1862 := by rfl
theorem patch_mem7_4_2_4 : RadiusFivePruning.patch7_4_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1862, parentRow_mem1862, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1862_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_2_4]
  rfl
theorem row_eq7_4_2_5 : RadiusFivePruning.stateRow7_4_2_5 = ParentOwnership.parentRow1864 := by rfl
theorem patch_mem7_4_2_5 : RadiusFivePruning.patch7_4_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1864, parentRow_mem1864, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1864_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_2_5]
  rfl
theorem row_eq7_4_2_6 : RadiusFivePruning.stateRow7_4_2_6 = ParentOwnership.parentRow0856 := by rfl
theorem patch_mem7_4_2_6 : RadiusFivePruning.patch7_4_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0856, parentRow_mem0856, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0856_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_2_6]
  rfl
theorem row_eq7_4_2_8 : RadiusFivePruning.stateRow7_4_2_8 = ParentOwnership.parentRow0969 := by rfl
theorem patch_mem7_4_2_8 : RadiusFivePruning.patch7_4_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0969, parentRow_mem0969, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0969_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_2_8]
  rfl
theorem row_eq7_4_2_10 : RadiusFivePruning.stateRow7_4_2_10 = ParentOwnership.parentRow0853 := by rfl
theorem patch_mem7_4_2_10 : RadiusFivePruning.patch7_4_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0853, parentRow_mem0853, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0853_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_2_10]
  rfl
theorem row_eq7_4_2_11 : RadiusFivePruning.stateRow7_4_2_11 = ParentOwnership.parentRow1853 := by rfl
theorem patch_mem7_4_2_11 : RadiusFivePruning.patch7_4_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1853, parentRow_mem1853, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1853_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_2_11]
  rfl
theorem chunk_mem7_4_2 : ∀ p ∈ RadiusFivePruning.final7_4_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_4_2, List.forall_mem_cons]
  exact ⟨patch_mem7_4_2_0,⟨patch_mem7_4_2_1,⟨patch_mem7_4_2_2,⟨patch_mem7_4_2_3,⟨patch_mem7_4_2_4,⟨patch_mem7_4_2_5,⟨patch_mem7_4_2_6,⟨patch_mem7_4_2_8,⟨patch_mem7_4_2_10,⟨patch_mem7_4_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_4_3_0 : RadiusFivePruning.stateRow7_4_3_0 = ParentOwnership.parentRow0649 := by rfl
theorem patch_mem7_4_3_0 : RadiusFivePruning.patch7_4_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0649, parentRow_mem0649, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0649_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_3_0]
  rfl
theorem row_eq7_4_3_1 : RadiusFivePruning.stateRow7_4_3_1 = ParentOwnership.parentRow1722 := by rfl
theorem patch_mem7_4_3_1 : RadiusFivePruning.patch7_4_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1722, parentRow_mem1722, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1722_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_3_1]
  rfl
theorem row_eq7_4_3_2 : RadiusFivePruning.stateRow7_4_3_2 = ParentOwnership.parentRow0650 := by rfl
theorem patch_mem7_4_3_2 : RadiusFivePruning.patch7_4_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0650, parentRow_mem0650, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0650_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_3_2]
  rfl
theorem row_eq7_4_3_3 : RadiusFivePruning.stateRow7_4_3_3 = ParentOwnership.parentRow1723 := by rfl
theorem patch_mem7_4_3_3 : RadiusFivePruning.patch7_4_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1723, parentRow_mem1723, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1723_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_3_3]
  rfl
theorem row_eq7_4_3_5 : RadiusFivePruning.stateRow7_4_3_5 = ParentOwnership.parentRow1272 := by rfl
theorem patch_mem7_4_3_5 : RadiusFivePruning.patch7_4_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1272, parentRow_mem1272, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1272_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_3_5]
  rfl
theorem row_eq7_4_3_6 : RadiusFivePruning.stateRow7_4_3_6 = ParentOwnership.parentRow1270 := by rfl
theorem patch_mem7_4_3_6 : RadiusFivePruning.patch7_4_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1270, parentRow_mem1270, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1270_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_3_6]
  rfl
theorem row_eq7_4_3_7 : RadiusFivePruning.stateRow7_4_3_7 = ParentOwnership.parentRow1686 := by rfl
theorem patch_mem7_4_3_7 : RadiusFivePruning.patch7_4_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1686, parentRow_mem1686, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1686_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_3_7]
  rfl
theorem row_eq7_4_3_8 : RadiusFivePruning.stateRow7_4_3_8 = ParentOwnership.parentRow1687 := by rfl
theorem patch_mem7_4_3_8 : RadiusFivePruning.patch7_4_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1687, parentRow_mem1687, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1687_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_3_8]
  rfl
theorem row_eq7_4_3_9 : RadiusFivePruning.stateRow7_4_3_9 = ParentOwnership.parentRow0521 := by rfl
theorem patch_mem7_4_3_9 : RadiusFivePruning.patch7_4_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0521, parentRow_mem0521, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0521_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_3_9]
  rfl
theorem row_eq7_4_3_10 : RadiusFivePruning.stateRow7_4_3_10 = ParentOwnership.parentRow0519 := by rfl
theorem patch_mem7_4_3_10 : RadiusFivePruning.patch7_4_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0519, parentRow_mem0519, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0519_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_3_10]
  rfl
theorem row_eq7_4_3_11 : RadiusFivePruning.stateRow7_4_3_11 = ParentOwnership.parentRow1269 := by rfl
theorem patch_mem7_4_3_11 : RadiusFivePruning.patch7_4_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1269, parentRow_mem1269, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1269_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_3_11]
  rfl
theorem chunk_mem7_4_3 : ∀ p ∈ RadiusFivePruning.final7_4_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_4_3, List.forall_mem_cons]
  exact ⟨patch_mem7_4_3_0,⟨patch_mem7_4_3_1,⟨patch_mem7_4_3_2,⟨patch_mem7_4_3_3,⟨patch_mem7_4_3_5,⟨patch_mem7_4_3_6,⟨patch_mem7_4_3_7,⟨patch_mem7_4_3_8,⟨patch_mem7_4_3_9,⟨patch_mem7_4_3_10,⟨patch_mem7_4_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_4_4_1 : RadiusFivePruning.stateRow7_4_4_1 = ParentOwnership.parentRow0968 := by rfl
theorem patch_mem7_4_4_1 : RadiusFivePruning.patch7_4_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0968, parentRow_mem0968, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0968_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_4_1]
  rfl
theorem row_eq7_4_4_2 : RadiusFivePruning.stateRow7_4_4_2 = ParentOwnership.parentRow1271 := by rfl
theorem patch_mem7_4_4_2 : RadiusFivePruning.patch7_4_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1271, parentRow_mem1271, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1271_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_4_2]
  rfl
theorem row_eq7_4_4_3 : RadiusFivePruning.stateRow7_4_4_3 = ParentOwnership.parentRow1688 := by rfl
theorem patch_mem7_4_4_3 : RadiusFivePruning.patch7_4_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1688, parentRow_mem1688, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1688_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_4_3]
  rfl
theorem row_eq7_4_4_4 : RadiusFivePruning.stateRow7_4_4_4 = ParentOwnership.parentRow1689 := by rfl
theorem patch_mem7_4_4_4 : RadiusFivePruning.patch7_4_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1689, parentRow_mem1689, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1689_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_4_4]
  rfl
theorem row_eq7_4_4_5 : RadiusFivePruning.stateRow7_4_4_5 = ParentOwnership.parentRow0520 := by rfl
theorem patch_mem7_4_4_5 : RadiusFivePruning.patch7_4_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0520, parentRow_mem0520, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0520_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_4_5]
  rfl
theorem row_eq7_4_4_8 : RadiusFivePruning.stateRow7_4_4_8 = ParentOwnership.parentRow1684 := by rfl
theorem patch_mem7_4_4_8 : RadiusFivePruning.patch7_4_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1684, parentRow_mem1684, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1684_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_4_8]
  rfl
theorem row_eq7_4_4_10 : RadiusFivePruning.stateRow7_4_4_10 = ParentOwnership.parentRow1268 := by rfl
theorem patch_mem7_4_4_10 : RadiusFivePruning.patch7_4_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1268, parentRow_mem1268, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1268_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_4_10]
  rfl
theorem chunk_mem7_4_4 : ∀ p ∈ RadiusFivePruning.final7_4_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_4_4, List.forall_mem_cons]
  exact ⟨patch_mem7_4_4_1,⟨patch_mem7_4_4_2,⟨patch_mem7_4_4_3,⟨patch_mem7_4_4_4,⟨patch_mem7_4_4_5,⟨patch_mem7_4_4_8,⟨patch_mem7_4_4_10,by simp⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_4_5_0 : RadiusFivePruning.stateRow7_4_5_0 = ParentOwnership.parentRow1685 := by rfl
theorem patch_mem7_4_5_0 : RadiusFivePruning.patch7_4_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1685, parentRow_mem1685, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1685_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_5_0]
  rfl
theorem row_eq7_4_5_2 : RadiusFivePruning.stateRow7_4_5_2 = ParentOwnership.parentRow0518 := by rfl
theorem patch_mem7_4_5_2 : RadiusFivePruning.patch7_4_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0518, parentRow_mem0518, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0518_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_5_2]
  rfl
theorem row_eq7_4_5_3 : RadiusFivePruning.stateRow7_4_5_3 = ParentOwnership.parentRow0516 := by rfl
theorem patch_mem7_4_5_3 : RadiusFivePruning.patch7_4_5_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0516, parentRow_mem0516, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0516_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_5_3]
  rfl
theorem row_eq7_4_5_4 : RadiusFivePruning.stateRow7_4_5_4 = ParentOwnership.parentRow1747 := by rfl
theorem patch_mem7_4_5_4 : RadiusFivePruning.patch7_4_5_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1747, parentRow_mem1747, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1747_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_5_4]
  rfl
theorem row_eq7_4_5_5 : RadiusFivePruning.stateRow7_4_5_5 = ParentOwnership.parentRow1737 := by rfl
theorem patch_mem7_4_5_5 : RadiusFivePruning.patch7_4_5_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1737, parentRow_mem1737, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1737_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_5_5]
  rfl
theorem row_eq7_4_5_6 : RadiusFivePruning.stateRow7_4_5_6 = ParentOwnership.parentRow1749 := by rfl
theorem patch_mem7_4_5_6 : RadiusFivePruning.patch7_4_5_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1749, parentRow_mem1749, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1749_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_5_6]
  rfl
theorem row_eq7_4_5_7 : RadiusFivePruning.stateRow7_4_5_7 = ParentOwnership.parentRow1728 := by rfl
theorem patch_mem7_4_5_7 : RadiusFivePruning.patch7_4_5_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1728, parentRow_mem1728, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1728_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_5_7]
  rfl
theorem row_eq7_4_5_8 : RadiusFivePruning.stateRow7_4_5_8 = ParentOwnership.parentRow1741 := by rfl
theorem patch_mem7_4_5_8 : RadiusFivePruning.patch7_4_5_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1741, parentRow_mem1741, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1741_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_5_8]
  rfl
theorem row_eq7_4_5_9 : RadiusFivePruning.stateRow7_4_5_9 = ParentOwnership.parentRow1743 := by rfl
theorem patch_mem7_4_5_9 : RadiusFivePruning.patch7_4_5_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1743, parentRow_mem1743, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1743_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_5_9]
  rfl
theorem row_eq7_4_5_10 : RadiusFivePruning.stateRow7_4_5_10 = ParentOwnership.parentRow1734 := by rfl
theorem patch_mem7_4_5_10 : RadiusFivePruning.patch7_4_5_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1734, parentRow_mem1734, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1734_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_5_10]
  rfl
theorem row_eq7_4_5_11 : RadiusFivePruning.stateRow7_4_5_11 = ParentOwnership.parentRow1748 := by rfl
theorem patch_mem7_4_5_11 : RadiusFivePruning.patch7_4_5_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1748, parentRow_mem1748, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1748_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_5_11]
  rfl
theorem chunk_mem7_4_5 : ∀ p ∈ RadiusFivePruning.final7_4_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_4_5, List.forall_mem_cons]
  exact ⟨patch_mem7_4_5_0,⟨patch_mem7_4_5_2,⟨patch_mem7_4_5_3,⟨patch_mem7_4_5_4,⟨patch_mem7_4_5_5,⟨patch_mem7_4_5_6,⟨patch_mem7_4_5_7,⟨patch_mem7_4_5_8,⟨patch_mem7_4_5_9,⟨patch_mem7_4_5_10,⟨patch_mem7_4_5_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
