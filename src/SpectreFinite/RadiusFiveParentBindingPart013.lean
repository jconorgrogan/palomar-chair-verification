module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock1T4C2
public import SpectreFinite.RadiusFivePruningLiteralBlock1T4C3
public import SpectreFinite.RadiusFivePruningLiteralBlock1T4C4
public import SpectreFinite.RadiusFivePruningLiteralBlock1T5C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq1_4_2_0 : RadiusFivePruning.stateRow1_4_2_0 = ParentOwnership.parentRow0523 := by rfl
theorem patch_mem1_4_2_0 : RadiusFivePruning.patch1_4_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0523, parentRow_mem0523, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0523_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_2_0]
  rfl
theorem row_eq1_4_2_1 : RadiusFivePruning.stateRow1_4_2_1 = ParentOwnership.parentRow1267 := by rfl
theorem patch_mem1_4_2_1 : RadiusFivePruning.patch1_4_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1267, parentRow_mem1267, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1267_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_2_1]
  rfl
theorem row_eq1_4_2_2 : RadiusFivePruning.stateRow1_4_2_2 = ParentOwnership.parentRow0524 := by rfl
theorem patch_mem1_4_2_2 : RadiusFivePruning.patch1_4_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0524, parentRow_mem0524, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0524_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_2_2]
  rfl
theorem row_eq1_4_2_3 : RadiusFivePruning.stateRow1_4_2_3 = ParentOwnership.parentRow0525 := by rfl
theorem patch_mem1_4_2_3 : RadiusFivePruning.patch1_4_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0525, parentRow_mem0525, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0525_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_2_3]
  rfl
theorem row_eq1_4_2_4 : RadiusFivePruning.stateRow1_4_2_4 = ParentOwnership.parentRow0515 := by rfl
theorem patch_mem1_4_2_4 : RadiusFivePruning.patch1_4_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0515, parentRow_mem0515, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0515_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_2_4]
  rfl
theorem row_eq1_4_2_6 : RadiusFivePruning.stateRow1_4_2_6 = ParentOwnership.parentRow1714 := by rfl
theorem patch_mem1_4_2_6 : RadiusFivePruning.patch1_4_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1714, parentRow_mem1714, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1714_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_2_6]
  rfl
theorem row_eq1_4_2_7 : RadiusFivePruning.stateRow1_4_2_7 = ParentOwnership.parentRow1715 := by rfl
theorem patch_mem1_4_2_7 : RadiusFivePruning.patch1_4_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1715, parentRow_mem1715, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1715_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_2_7]
  rfl
theorem row_eq1_4_2_8 : RadiusFivePruning.stateRow1_4_2_8 = ParentOwnership.parentRow1718 := by rfl
theorem patch_mem1_4_2_8 : RadiusFivePruning.patch1_4_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1718, parentRow_mem1718, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1718_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_2_8]
  rfl
theorem row_eq1_4_2_9 : RadiusFivePruning.stateRow1_4_2_9 = ParentOwnership.parentRow0537 := by rfl
theorem patch_mem1_4_2_9 : RadiusFivePruning.patch1_4_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0537, parentRow_mem0537, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0537_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_2_9]
  rfl
theorem row_eq1_4_2_11 : RadiusFivePruning.stateRow1_4_2_11 = ParentOwnership.parentRow1717 := by rfl
theorem patch_mem1_4_2_11 : RadiusFivePruning.patch1_4_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1717, parentRow_mem1717, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1717_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_2_11]
  rfl
theorem chunk_mem1_4_2 : ∀ p ∈ RadiusFivePruning.final1_4_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_4_2, List.forall_mem_cons]
  exact ⟨patch_mem1_4_2_0,⟨patch_mem1_4_2_1,⟨patch_mem1_4_2_2,⟨patch_mem1_4_2_3,⟨patch_mem1_4_2_4,⟨patch_mem1_4_2_6,⟨patch_mem1_4_2_7,⟨patch_mem1_4_2_8,⟨patch_mem1_4_2_9,⟨patch_mem1_4_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_4_3_0 : RadiusFivePruning.stateRow1_4_3_0 = ParentOwnership.parentRow0536 := by rfl
theorem patch_mem1_4_3_0 : RadiusFivePruning.patch1_4_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0536, parentRow_mem0536, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0536_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_3_0]
  rfl
theorem row_eq1_4_3_1 : RadiusFivePruning.stateRow1_4_3_1 = ParentOwnership.parentRow1739 := by rfl
theorem patch_mem1_4_3_1 : RadiusFivePruning.patch1_4_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1739, parentRow_mem1739, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1739_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_3_1]
  rfl
theorem row_eq1_4_3_3 : RadiusFivePruning.stateRow1_4_3_3 = ParentOwnership.parentRow1694 := by rfl
theorem patch_mem1_4_3_3 : RadiusFivePruning.patch1_4_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1694, parentRow_mem1694, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1694_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_3_3]
  rfl
theorem row_eq1_4_3_5 : RadiusFivePruning.stateRow1_4_3_5 = ParentOwnership.parentRow1697 := by rfl
theorem patch_mem1_4_3_5 : RadiusFivePruning.patch1_4_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1697, parentRow_mem1697, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1697_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_3_5]
  rfl
theorem row_eq1_4_3_6 : RadiusFivePruning.stateRow1_4_3_6 = ParentOwnership.parentRow1732 := by rfl
theorem patch_mem1_4_3_6 : RadiusFivePruning.patch1_4_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1732, parentRow_mem1732, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1732_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_3_6]
  rfl
theorem row_eq1_4_3_7 : RadiusFivePruning.stateRow1_4_3_7 = ParentOwnership.parentRow1740 := by rfl
theorem patch_mem1_4_3_7 : RadiusFivePruning.patch1_4_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1740, parentRow_mem1740, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1740_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_3_7]
  rfl
theorem row_eq1_4_3_8 : RadiusFivePruning.stateRow1_4_3_8 = ParentOwnership.parentRow1696 := by rfl
theorem patch_mem1_4_3_8 : RadiusFivePruning.patch1_4_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1696, parentRow_mem1696, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1696_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_3_8]
  rfl
theorem row_eq1_4_3_9 : RadiusFivePruning.stateRow1_4_3_9 = ParentOwnership.parentRow1731 := by rfl
theorem patch_mem1_4_3_9 : RadiusFivePruning.patch1_4_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1731, parentRow_mem1731, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1731_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_3_9]
  rfl
theorem row_eq1_4_3_10 : RadiusFivePruning.stateRow1_4_3_10 = ParentOwnership.parentRow1745 := by rfl
theorem patch_mem1_4_3_10 : RadiusFivePruning.patch1_4_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1745, parentRow_mem1745, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1745_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_3_10]
  rfl
theorem row_eq1_4_3_11 : RadiusFivePruning.stateRow1_4_3_11 = ParentOwnership.parentRow1695 := by rfl
theorem patch_mem1_4_3_11 : RadiusFivePruning.patch1_4_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1695, parentRow_mem1695, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1695_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_3_11]
  rfl
theorem chunk_mem1_4_3 : ∀ p ∈ RadiusFivePruning.final1_4_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_4_3, List.forall_mem_cons]
  exact ⟨patch_mem1_4_3_0,⟨patch_mem1_4_3_1,⟨patch_mem1_4_3_3,⟨patch_mem1_4_3_5,⟨patch_mem1_4_3_6,⟨patch_mem1_4_3_7,⟨patch_mem1_4_3_8,⟨patch_mem1_4_3_9,⟨patch_mem1_4_3_10,⟨patch_mem1_4_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_4_4_1 : RadiusFivePruning.stateRow1_4_4_1 = ParentOwnership.parentRow1698 := by rfl
theorem patch_mem1_4_4_1 : RadiusFivePruning.patch1_4_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1698, parentRow_mem1698, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1698_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_4_1]
  rfl
theorem row_eq1_4_4_2 : RadiusFivePruning.stateRow1_4_4_2 = ParentOwnership.parentRow1733 := by rfl
theorem patch_mem1_4_4_2 : RadiusFivePruning.patch1_4_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1733, parentRow_mem1733, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1733_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_4_2]
  rfl
theorem row_eq1_4_4_4 : RadiusFivePruning.stateRow1_4_4_4 = ParentOwnership.parentRow1753 := by rfl
theorem patch_mem1_4_4_4 : RadiusFivePruning.patch1_4_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1753, parentRow_mem1753, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1753_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_4_4]
  rfl
theorem row_eq1_4_4_7 : RadiusFivePruning.stateRow1_4_4_7 = ParentOwnership.parentRow2073 := by rfl
theorem patch_mem1_4_4_7 : RadiusFivePruning.patch1_4_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2073, parentRow_mem2073, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2073_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_4_7]
  rfl
theorem row_eq1_4_4_9 : RadiusFivePruning.stateRow1_4_4_9 = ParentOwnership.parentRow2072 := by rfl
theorem patch_mem1_4_4_9 : RadiusFivePruning.patch1_4_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2072, parentRow_mem2072, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2072_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_4_9]
  rfl
theorem row_eq1_4_4_10 : RadiusFivePruning.stateRow1_4_4_10 = ParentOwnership.parentRow1758 := by rfl
theorem patch_mem1_4_4_10 : RadiusFivePruning.patch1_4_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1758, parentRow_mem1758, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1758_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_4_10]
  rfl
theorem chunk_mem1_4_4 : ∀ p ∈ RadiusFivePruning.final1_4_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_4_4, List.forall_mem_cons]
  exact ⟨patch_mem1_4_4_1,⟨patch_mem1_4_4_2,⟨patch_mem1_4_4_4,⟨patch_mem1_4_4_7,⟨patch_mem1_4_4_9,⟨patch_mem1_4_4_10,by simp⟩⟩⟩⟩⟩⟩
theorem row_eq1_5_0_1 : RadiusFivePruning.stateRow1_5_0_1 = ParentOwnership.parentRow1013 := by rfl
theorem patch_mem1_5_0_1 : RadiusFivePruning.patch1_5_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1013, parentRow_mem1013, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1013_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_0_1]
  rfl
theorem row_eq1_5_0_2 : RadiusFivePruning.stateRow1_5_0_2 = ParentOwnership.parentRow2077 := by rfl
theorem patch_mem1_5_0_2 : RadiusFivePruning.patch1_5_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2077, parentRow_mem2077, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2077_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_0_2]
  rfl
theorem row_eq1_5_0_3 : RadiusFivePruning.stateRow1_5_0_3 = ParentOwnership.parentRow2078 := by rfl
theorem patch_mem1_5_0_3 : RadiusFivePruning.patch1_5_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2078, parentRow_mem2078, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2078_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_0_3]
  rfl
theorem row_eq1_5_0_5 : RadiusFivePruning.stateRow1_5_0_5 = ParentOwnership.parentRow2076 := by rfl
theorem patch_mem1_5_0_5 : RadiusFivePruning.patch1_5_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2076, parentRow_mem2076, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2076_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_0_5]
  rfl
theorem row_eq1_5_0_6 : RadiusFivePruning.stateRow1_5_0_6 = ParentOwnership.parentRow2079 := by rfl
theorem patch_mem1_5_0_6 : RadiusFivePruning.patch1_5_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2079, parentRow_mem2079, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2079_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_0_6]
  rfl
theorem row_eq1_5_0_7 : RadiusFivePruning.stateRow1_5_0_7 = ParentOwnership.parentRow2080 := by rfl
theorem patch_mem1_5_0_7 : RadiusFivePruning.patch1_5_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2080, parentRow_mem2080, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2080_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_0_7]
  rfl
theorem row_eq1_5_0_8 : RadiusFivePruning.stateRow1_5_0_8 = ParentOwnership.parentRow2081 := by rfl
theorem patch_mem1_5_0_8 : RadiusFivePruning.patch1_5_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2081, parentRow_mem2081, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2081_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_0_8]
  rfl
theorem row_eq1_5_0_9 : RadiusFivePruning.stateRow1_5_0_9 = ParentOwnership.parentRow2082 := by rfl
theorem patch_mem1_5_0_9 : RadiusFivePruning.patch1_5_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2082, parentRow_mem2082, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2082_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_0_9]
  rfl
theorem row_eq1_5_0_10 : RadiusFivePruning.stateRow1_5_0_10 = ParentOwnership.parentRow1014 := by rfl
theorem patch_mem1_5_0_10 : RadiusFivePruning.patch1_5_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1014, parentRow_mem1014, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1014_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_0_10]
  rfl
theorem row_eq1_5_0_11 : RadiusFivePruning.stateRow1_5_0_11 = ParentOwnership.parentRow1015 := by rfl
theorem patch_mem1_5_0_11 : RadiusFivePruning.patch1_5_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1015, parentRow_mem1015, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1015_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_0_11]
  rfl
theorem chunk_mem1_5_0 : ∀ p ∈ RadiusFivePruning.final1_5_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_5_0, List.forall_mem_cons]
  exact ⟨patch_mem1_5_0_1,⟨patch_mem1_5_0_2,⟨patch_mem1_5_0_3,⟨patch_mem1_5_0_5,⟨patch_mem1_5_0_6,⟨patch_mem1_5_0_7,⟨patch_mem1_5_0_8,⟨patch_mem1_5_0_9,⟨patch_mem1_5_0_10,⟨patch_mem1_5_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
