module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock1T0C2
public import SpectreFinite.RadiusFivePruningLiteralBlock1T0C3
public import SpectreFinite.RadiusFivePruningLiteralBlock1T0C4
public import SpectreFinite.RadiusFivePruningLiteralBlock1T1C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq1_0_2_0 : RadiusFivePruning.stateRow1_0_2_0 = ParentOwnership.parentRow1926 := by rfl
theorem patch_mem1_0_2_0 : RadiusFivePruning.patch1_0_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1926, parentRow_mem1926, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1926_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_2_0]
  rfl
theorem row_eq1_0_2_1 : RadiusFivePruning.stateRow1_0_2_1 = ParentOwnership.parentRow1927 := by rfl
theorem patch_mem1_0_2_1 : RadiusFivePruning.patch1_0_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1927, parentRow_mem1927, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1927_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_2_1]
  rfl
theorem row_eq1_0_2_2 : RadiusFivePruning.stateRow1_0_2_2 = ParentOwnership.parentRow1928 := by rfl
theorem patch_mem1_0_2_2 : RadiusFivePruning.patch1_0_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1928, parentRow_mem1928, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1928_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_2_2]
  rfl
theorem row_eq1_0_2_3 : RadiusFivePruning.stateRow1_0_2_3 = ParentOwnership.parentRow1929 := by rfl
theorem patch_mem1_0_2_3 : RadiusFivePruning.patch1_0_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1929, parentRow_mem1929, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1929_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_2_3]
  rfl
theorem row_eq1_0_2_4 : RadiusFivePruning.stateRow1_0_2_4 = ParentOwnership.parentRow1930 := by rfl
theorem patch_mem1_0_2_4 : RadiusFivePruning.patch1_0_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1930, parentRow_mem1930, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1930_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_2_4]
  rfl
theorem row_eq1_0_2_6 : RadiusFivePruning.stateRow1_0_2_6 = ParentOwnership.parentRow0681 := by rfl
theorem patch_mem1_0_2_6 : RadiusFivePruning.patch1_0_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0681, parentRow_mem0681, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0681_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_2_6]
  rfl
theorem row_eq1_0_2_7 : RadiusFivePruning.stateRow1_0_2_7 = ParentOwnership.parentRow0682 := by rfl
theorem patch_mem1_0_2_7 : RadiusFivePruning.patch1_0_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0682, parentRow_mem0682, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0682_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_2_7]
  rfl
theorem row_eq1_0_2_8 : RadiusFivePruning.stateRow1_0_2_8 = ParentOwnership.parentRow0683 := by rfl
theorem patch_mem1_0_2_8 : RadiusFivePruning.patch1_0_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0683, parentRow_mem0683, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0683_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_2_8]
  rfl
theorem row_eq1_0_2_9 : RadiusFivePruning.stateRow1_0_2_9 = ParentOwnership.parentRow0684 := by rfl
theorem patch_mem1_0_2_9 : RadiusFivePruning.patch1_0_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0684, parentRow_mem0684, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0684_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_2_9]
  rfl
theorem row_eq1_0_2_11 : RadiusFivePruning.stateRow1_0_2_11 = ParentOwnership.parentRow0685 := by rfl
theorem patch_mem1_0_2_11 : RadiusFivePruning.patch1_0_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0685, parentRow_mem0685, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0685_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_2_11]
  rfl
theorem chunk_mem1_0_2 : ∀ p ∈ RadiusFivePruning.final1_0_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_0_2, List.forall_mem_cons]
  exact ⟨patch_mem1_0_2_0,⟨patch_mem1_0_2_1,⟨patch_mem1_0_2_2,⟨patch_mem1_0_2_3,⟨patch_mem1_0_2_4,⟨patch_mem1_0_2_6,⟨patch_mem1_0_2_7,⟨patch_mem1_0_2_8,⟨patch_mem1_0_2_9,⟨patch_mem1_0_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_0_3_0 : RadiusFivePruning.stateRow1_0_3_0 = ParentOwnership.parentRow0686 := by rfl
theorem patch_mem1_0_3_0 : RadiusFivePruning.patch1_0_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0686, parentRow_mem0686, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0686_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_3_0]
  rfl
theorem row_eq1_0_3_1 : RadiusFivePruning.stateRow1_0_3_1 = ParentOwnership.parentRow0687 := by rfl
theorem patch_mem1_0_3_1 : RadiusFivePruning.patch1_0_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0687, parentRow_mem0687, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0687_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_3_1]
  rfl
theorem row_eq1_0_3_3 : RadiusFivePruning.stateRow1_0_3_3 = ParentOwnership.parentRow0561 := by rfl
theorem patch_mem1_0_3_3 : RadiusFivePruning.patch1_0_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0561, parentRow_mem0561, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0561_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_3_3]
  rfl
theorem row_eq1_0_3_5 : RadiusFivePruning.stateRow1_0_3_5 = ParentOwnership.parentRow0562 := by rfl
theorem patch_mem1_0_3_5 : RadiusFivePruning.patch1_0_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0562, parentRow_mem0562, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0562_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_3_5]
  rfl
theorem row_eq1_0_3_6 : RadiusFivePruning.stateRow1_0_3_6 = ParentOwnership.parentRow0563 := by rfl
theorem patch_mem1_0_3_6 : RadiusFivePruning.patch1_0_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0563, parentRow_mem0563, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0563_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_3_6]
  rfl
theorem row_eq1_0_3_7 : RadiusFivePruning.stateRow1_0_3_7 = ParentOwnership.parentRow0564 := by rfl
theorem patch_mem1_0_3_7 : RadiusFivePruning.patch1_0_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0564, parentRow_mem0564, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0564_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_3_7]
  rfl
theorem row_eq1_0_3_8 : RadiusFivePruning.stateRow1_0_3_8 = ParentOwnership.parentRow0565 := by rfl
theorem patch_mem1_0_3_8 : RadiusFivePruning.patch1_0_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0565, parentRow_mem0565, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0565_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_3_8]
  rfl
theorem row_eq1_0_3_9 : RadiusFivePruning.stateRow1_0_3_9 = ParentOwnership.parentRow0566 := by rfl
theorem patch_mem1_0_3_9 : RadiusFivePruning.patch1_0_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0566, parentRow_mem0566, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0566_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_3_9]
  rfl
theorem row_eq1_0_3_10 : RadiusFivePruning.stateRow1_0_3_10 = ParentOwnership.parentRow0552 := by rfl
theorem patch_mem1_0_3_10 : RadiusFivePruning.patch1_0_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0552, parentRow_mem0552, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0552_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_3_10]
  rfl
theorem row_eq1_0_3_11 : RadiusFivePruning.stateRow1_0_3_11 = ParentOwnership.parentRow0553 := by rfl
theorem patch_mem1_0_3_11 : RadiusFivePruning.patch1_0_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0553, parentRow_mem0553, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0553_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_3_11]
  rfl
theorem chunk_mem1_0_3 : ∀ p ∈ RadiusFivePruning.final1_0_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_0_3, List.forall_mem_cons]
  exact ⟨patch_mem1_0_3_0,⟨patch_mem1_0_3_1,⟨patch_mem1_0_3_3,⟨patch_mem1_0_3_5,⟨patch_mem1_0_3_6,⟨patch_mem1_0_3_7,⟨patch_mem1_0_3_8,⟨patch_mem1_0_3_9,⟨patch_mem1_0_3_10,⟨patch_mem1_0_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_0_4_1 : RadiusFivePruning.stateRow1_0_4_1 = ParentOwnership.parentRow0554 := by rfl
theorem patch_mem1_0_4_1 : RadiusFivePruning.patch1_0_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0554, parentRow_mem0554, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0554_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_4_1]
  rfl
theorem row_eq1_0_4_2 : RadiusFivePruning.stateRow1_0_4_2 = ParentOwnership.parentRow0555 := by rfl
theorem patch_mem1_0_4_2 : RadiusFivePruning.patch1_0_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0555, parentRow_mem0555, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0555_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_4_2]
  rfl
theorem row_eq1_0_4_4 : RadiusFivePruning.stateRow1_0_4_4 = ParentOwnership.parentRow0630 := by rfl
theorem patch_mem1_0_4_4 : RadiusFivePruning.patch1_0_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0630, parentRow_mem0630, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0630_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_4_4]
  rfl
theorem row_eq1_0_4_7 : RadiusFivePruning.stateRow1_0_4_7 = ParentOwnership.parentRow0642 := by rfl
theorem patch_mem1_0_4_7 : RadiusFivePruning.patch1_0_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0642, parentRow_mem0642, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0642_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_4_7]
  rfl
theorem row_eq1_0_4_9 : RadiusFivePruning.stateRow1_0_4_9 = ParentOwnership.parentRow0645 := by rfl
theorem patch_mem1_0_4_9 : RadiusFivePruning.patch1_0_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0645, parentRow_mem0645, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0645_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_4_9]
  rfl
theorem row_eq1_0_4_10 : RadiusFivePruning.stateRow1_0_4_10 = ParentOwnership.parentRow0646 := by rfl
theorem patch_mem1_0_4_10 : RadiusFivePruning.patch1_0_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0646, parentRow_mem0646, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0646_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_0_4_10]
  rfl
theorem chunk_mem1_0_4 : ∀ p ∈ RadiusFivePruning.final1_0_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_0_4, List.forall_mem_cons]
  exact ⟨patch_mem1_0_4_1,⟨patch_mem1_0_4_2,⟨patch_mem1_0_4_4,⟨patch_mem1_0_4_7,⟨patch_mem1_0_4_9,⟨patch_mem1_0_4_10,by simp⟩⟩⟩⟩⟩⟩
theorem row_eq1_1_0_1 : RadiusFivePruning.stateRow1_1_0_1 = ParentOwnership.parentRow1300 := by rfl
theorem patch_mem1_1_0_1 : RadiusFivePruning.patch1_1_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1300, parentRow_mem1300, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1300_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_0_1]
  rfl
theorem row_eq1_1_0_2 : RadiusFivePruning.stateRow1_1_0_2 = ParentOwnership.parentRow1764 := by rfl
theorem patch_mem1_1_0_2 : RadiusFivePruning.patch1_1_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1764, parentRow_mem1764, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1764_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_0_2]
  rfl
theorem row_eq1_1_0_3 : RadiusFivePruning.stateRow1_1_0_3 = ParentOwnership.parentRow1765 := by rfl
theorem patch_mem1_1_0_3 : RadiusFivePruning.patch1_1_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1765, parentRow_mem1765, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1765_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_0_3]
  rfl
theorem row_eq1_1_0_5 : RadiusFivePruning.stateRow1_1_0_5 = ParentOwnership.parentRow1768 := by rfl
theorem patch_mem1_1_0_5 : RadiusFivePruning.patch1_1_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1768, parentRow_mem1768, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1768_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_0_5]
  rfl
theorem row_eq1_1_0_6 : RadiusFivePruning.stateRow1_1_0_6 = ParentOwnership.parentRow1783 := by rfl
theorem patch_mem1_1_0_6 : RadiusFivePruning.patch1_1_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1783, parentRow_mem1783, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1783_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_0_6]
  rfl
theorem row_eq1_1_0_7 : RadiusFivePruning.stateRow1_1_0_7 = ParentOwnership.parentRow1785 := by rfl
theorem patch_mem1_1_0_7 : RadiusFivePruning.patch1_1_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1785, parentRow_mem1785, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1785_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_0_7]
  rfl
theorem row_eq1_1_0_8 : RadiusFivePruning.stateRow1_1_0_8 = ParentOwnership.parentRow1790 := by rfl
theorem patch_mem1_1_0_8 : RadiusFivePruning.patch1_1_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1790, parentRow_mem1790, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1790_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_0_8]
  rfl
theorem row_eq1_1_0_9 : RadiusFivePruning.stateRow1_1_0_9 = ParentOwnership.parentRow1792 := by rfl
theorem patch_mem1_1_0_9 : RadiusFivePruning.patch1_1_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1792, parentRow_mem1792, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1792_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_0_9]
  rfl
theorem row_eq1_1_0_10 : RadiusFivePruning.stateRow1_1_0_10 = ParentOwnership.parentRow1766 := by rfl
theorem patch_mem1_1_0_10 : RadiusFivePruning.patch1_1_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1766, parentRow_mem1766, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1766_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_0_10]
  rfl
theorem row_eq1_1_0_11 : RadiusFivePruning.stateRow1_1_0_11 = ParentOwnership.parentRow1767 := by rfl
theorem patch_mem1_1_0_11 : RadiusFivePruning.patch1_1_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1767, parentRow_mem1767, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1767_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_0_11]
  rfl
theorem chunk_mem1_1_0 : ∀ p ∈ RadiusFivePruning.final1_1_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_1_0, List.forall_mem_cons]
  exact ⟨patch_mem1_1_0_1,⟨patch_mem1_1_0_2,⟨patch_mem1_1_0_3,⟨patch_mem1_1_0_5,⟨patch_mem1_1_0_6,⟨patch_mem1_1_0_7,⟨patch_mem1_1_0_8,⟨patch_mem1_1_0_9,⟨patch_mem1_1_0_10,⟨patch_mem1_1_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
