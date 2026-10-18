module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock1T1C1
public import SpectreFinite.RadiusFivePruningLiteralBlock1T1C2
public import SpectreFinite.RadiusFivePruningLiteralBlock1T1C3
public import SpectreFinite.RadiusFivePruningLiteralBlock1T1C4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq1_1_1_1 : RadiusFivePruning.stateRow1_1_1_1 = ParentOwnership.parentRow1784 := by rfl
theorem patch_mem1_1_1_1 : RadiusFivePruning.patch1_1_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1784, parentRow_mem1784, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1784_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_1_1]
  rfl
theorem row_eq1_1_1_2 : RadiusFivePruning.stateRow1_1_1_2 = ParentOwnership.parentRow1786 := by rfl
theorem patch_mem1_1_1_2 : RadiusFivePruning.patch1_1_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1786, parentRow_mem1786, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1786_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_1_2]
  rfl
theorem row_eq1_1_1_3 : RadiusFivePruning.stateRow1_1_1_3 = ParentOwnership.parentRow1791 := by rfl
theorem patch_mem1_1_1_3 : RadiusFivePruning.patch1_1_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1791, parentRow_mem1791, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1791_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_1_3]
  rfl
theorem row_eq1_1_1_4 : RadiusFivePruning.stateRow1_1_1_4 = ParentOwnership.parentRow1793 := by rfl
theorem patch_mem1_1_1_4 : RadiusFivePruning.patch1_1_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1793, parentRow_mem1793, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1793_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_1_4]
  rfl
theorem row_eq1_1_1_5 : RadiusFivePruning.stateRow1_1_1_5 = ParentOwnership.parentRow1763 := by rfl
theorem patch_mem1_1_1_5 : RadiusFivePruning.patch1_1_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1763, parentRow_mem1763, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1763_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_1_5]
  rfl
theorem row_eq1_1_1_6 : RadiusFivePruning.stateRow1_1_1_6 = ParentOwnership.parentRow1782 := by rfl
theorem patch_mem1_1_1_6 : RadiusFivePruning.patch1_1_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1782, parentRow_mem1782, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1782_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_1_6]
  rfl
theorem row_eq1_1_1_8 : RadiusFivePruning.stateRow1_1_1_8 = ParentOwnership.parentRow1789 := by rfl
theorem patch_mem1_1_1_8 : RadiusFivePruning.patch1_1_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1789, parentRow_mem1789, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1789_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_1_8]
  rfl
theorem row_eq1_1_1_9 : RadiusFivePruning.stateRow1_1_1_9 = ParentOwnership.parentRow1801 := by rfl
theorem patch_mem1_1_1_9 : RadiusFivePruning.patch1_1_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1801, parentRow_mem1801, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1801_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_1_9]
  rfl
theorem row_eq1_1_1_10 : RadiusFivePruning.stateRow1_1_1_10 = ParentOwnership.parentRow1800 := by rfl
theorem patch_mem1_1_1_10 : RadiusFivePruning.patch1_1_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1800, parentRow_mem1800, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1800_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_1_10]
  rfl
theorem chunk_mem1_1_1 : ∀ p ∈ RadiusFivePruning.final1_1_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_1_1, List.forall_mem_cons]
  exact ⟨patch_mem1_1_1_1,⟨patch_mem1_1_1_2,⟨patch_mem1_1_1_3,⟨patch_mem1_1_1_4,⟨patch_mem1_1_1_5,⟨patch_mem1_1_1_6,⟨patch_mem1_1_1_8,⟨patch_mem1_1_1_9,⟨patch_mem1_1_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_1_2_0 : RadiusFivePruning.stateRow1_1_2_0 = ParentOwnership.parentRow1781 := by rfl
theorem patch_mem1_1_2_0 : RadiusFivePruning.patch1_1_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1781, parentRow_mem1781, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1781_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_2_0]
  rfl
theorem row_eq1_1_2_1 : RadiusFivePruning.stateRow1_1_2_1 = ParentOwnership.parentRow1798 := by rfl
theorem patch_mem1_1_2_1 : RadiusFivePruning.patch1_1_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1798, parentRow_mem1798, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1798_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_2_1]
  rfl
theorem row_eq1_1_2_2 : RadiusFivePruning.stateRow1_1_2_2 = ParentOwnership.parentRow1788 := by rfl
theorem patch_mem1_1_2_2 : RadiusFivePruning.patch1_1_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1788, parentRow_mem1788, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1788_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_2_2]
  rfl
theorem row_eq1_1_2_3 : RadiusFivePruning.stateRow1_1_2_3 = ParentOwnership.parentRow1799 := by rfl
theorem patch_mem1_1_2_3 : RadiusFivePruning.patch1_1_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1799, parentRow_mem1799, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1799_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_2_3]
  rfl
theorem row_eq1_1_2_4 : RadiusFivePruning.stateRow1_1_2_4 = ParentOwnership.parentRow1797 := by rfl
theorem patch_mem1_1_2_4 : RadiusFivePruning.patch1_1_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1797, parentRow_mem1797, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1797_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_2_4]
  rfl
theorem row_eq1_1_2_6 : RadiusFivePruning.stateRow1_1_2_6 = ParentOwnership.parentRow0585 := by rfl
theorem patch_mem1_1_2_6 : RadiusFivePruning.patch1_1_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0585, parentRow_mem0585, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0585_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_2_6]
  rfl
theorem row_eq1_1_2_7 : RadiusFivePruning.stateRow1_1_2_7 = ParentOwnership.parentRow0826 := by rfl
theorem patch_mem1_1_2_7 : RadiusFivePruning.patch1_1_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0826, parentRow_mem0826, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0826_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_2_7]
  rfl
theorem row_eq1_1_2_8 : RadiusFivePruning.stateRow1_1_2_8 = ParentOwnership.parentRow0833 := by rfl
theorem patch_mem1_1_2_8 : RadiusFivePruning.patch1_1_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0833, parentRow_mem0833, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0833_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_2_8]
  rfl
theorem row_eq1_1_2_9 : RadiusFivePruning.stateRow1_1_2_9 = ParentOwnership.parentRow0834 := by rfl
theorem patch_mem1_1_2_9 : RadiusFivePruning.patch1_1_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0834, parentRow_mem0834, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0834_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_2_9]
  rfl
theorem row_eq1_1_2_11 : RadiusFivePruning.stateRow1_1_2_11 = ParentOwnership.parentRow0842 := by rfl
theorem patch_mem1_1_2_11 : RadiusFivePruning.patch1_1_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0842, parentRow_mem0842, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0842_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_2_11]
  rfl
theorem chunk_mem1_1_2 : ∀ p ∈ RadiusFivePruning.final1_1_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_1_2, List.forall_mem_cons]
  exact ⟨patch_mem1_1_2_0,⟨patch_mem1_1_2_1,⟨patch_mem1_1_2_2,⟨patch_mem1_1_2_3,⟨patch_mem1_1_2_4,⟨patch_mem1_1_2_6,⟨patch_mem1_1_2_7,⟨patch_mem1_1_2_8,⟨patch_mem1_1_2_9,⟨patch_mem1_1_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_1_3_0 : RadiusFivePruning.stateRow1_1_3_0 = ParentOwnership.parentRow0843 := by rfl
theorem patch_mem1_1_3_0 : RadiusFivePruning.patch1_1_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0843, parentRow_mem0843, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0843_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_3_0]
  rfl
theorem row_eq1_1_3_1 : RadiusFivePruning.stateRow1_1_3_1 = ParentOwnership.parentRow0844 := by rfl
theorem patch_mem1_1_3_1 : RadiusFivePruning.patch1_1_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0844, parentRow_mem0844, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0844_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_3_1]
  rfl
theorem row_eq1_1_3_3 : RadiusFivePruning.stateRow1_1_3_3 = ParentOwnership.parentRow0827 := by rfl
theorem patch_mem1_1_3_3 : RadiusFivePruning.patch1_1_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0827, parentRow_mem0827, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0827_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_3_3]
  rfl
theorem row_eq1_1_3_5 : RadiusFivePruning.stateRow1_1_3_5 = ParentOwnership.parentRow0835 := by rfl
theorem patch_mem1_1_3_5 : RadiusFivePruning.patch1_1_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0835, parentRow_mem0835, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0835_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_3_5]
  rfl
theorem row_eq1_1_3_6 : RadiusFivePruning.stateRow1_1_3_6 = ParentOwnership.parentRow0836 := by rfl
theorem patch_mem1_1_3_6 : RadiusFivePruning.patch1_1_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0836, parentRow_mem0836, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0836_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_3_6]
  rfl
theorem row_eq1_1_3_7 : RadiusFivePruning.stateRow1_1_3_7 = ParentOwnership.parentRow0847 := by rfl
theorem patch_mem1_1_3_7 : RadiusFivePruning.patch1_1_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0847, parentRow_mem0847, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0847_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_3_7]
  rfl
theorem row_eq1_1_3_8 : RadiusFivePruning.stateRow1_1_3_8 = ParentOwnership.parentRow0846 := by rfl
theorem patch_mem1_1_3_8 : RadiusFivePruning.patch1_1_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0846, parentRow_mem0846, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0846_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_3_8]
  rfl
theorem row_eq1_1_3_9 : RadiusFivePruning.stateRow1_1_3_9 = ParentOwnership.parentRow0848 := by rfl
theorem patch_mem1_1_3_9 : RadiusFivePruning.patch1_1_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0848, parentRow_mem0848, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0848_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_3_9]
  rfl
theorem row_eq1_1_3_10 : RadiusFivePruning.stateRow1_1_3_10 = ParentOwnership.parentRow0919 := by rfl
theorem patch_mem1_1_3_10 : RadiusFivePruning.patch1_1_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0919, parentRow_mem0919, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0919_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_3_10]
  rfl
theorem row_eq1_1_3_11 : RadiusFivePruning.stateRow1_1_3_11 = ParentOwnership.parentRow0830 := by rfl
theorem patch_mem1_1_3_11 : RadiusFivePruning.patch1_1_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0830, parentRow_mem0830, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0830_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_3_11]
  rfl
theorem chunk_mem1_1_3 : ∀ p ∈ RadiusFivePruning.final1_1_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_1_3, List.forall_mem_cons]
  exact ⟨patch_mem1_1_3_0,⟨patch_mem1_1_3_1,⟨patch_mem1_1_3_3,⟨patch_mem1_1_3_5,⟨patch_mem1_1_3_6,⟨patch_mem1_1_3_7,⟨patch_mem1_1_3_8,⟨patch_mem1_1_3_9,⟨patch_mem1_1_3_10,⟨patch_mem1_1_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_1_4_1 : RadiusFivePruning.stateRow1_1_4_1 = ParentOwnership.parentRow0837 := by rfl
theorem patch_mem1_1_4_1 : RadiusFivePruning.patch1_1_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0837, parentRow_mem0837, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0837_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_4_1]
  rfl
theorem row_eq1_1_4_2 : RadiusFivePruning.stateRow1_1_4_2 = ParentOwnership.parentRow0838 := by rfl
theorem patch_mem1_1_4_2 : RadiusFivePruning.patch1_1_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0838, parentRow_mem0838, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0838_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_4_2]
  rfl
theorem row_eq1_1_4_4 : RadiusFivePruning.stateRow1_1_4_4 = ParentOwnership.parentRow0920 := by rfl
theorem patch_mem1_1_4_4 : RadiusFivePruning.patch1_1_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0920, parentRow_mem0920, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0920_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_4_4]
  rfl
theorem row_eq1_1_4_7 : RadiusFivePruning.stateRow1_1_4_7 = ParentOwnership.parentRow0754 := by rfl
theorem patch_mem1_1_4_7 : RadiusFivePruning.patch1_1_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0754, parentRow_mem0754, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0754_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_4_7]
  rfl
theorem row_eq1_1_4_9 : RadiusFivePruning.stateRow1_1_4_9 = ParentOwnership.parentRow1985 := by rfl
theorem patch_mem1_1_4_9 : RadiusFivePruning.patch1_1_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1985, parentRow_mem1985, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1985_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_4_9]
  rfl
theorem row_eq1_1_4_10 : RadiusFivePruning.stateRow1_1_4_10 = ParentOwnership.parentRow1986 := by rfl
theorem patch_mem1_1_4_10 : RadiusFivePruning.patch1_1_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1986, parentRow_mem1986, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1986_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_1_4_10]
  rfl
theorem chunk_mem1_1_4 : ∀ p ∈ RadiusFivePruning.final1_1_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_1_4, List.forall_mem_cons]
  exact ⟨patch_mem1_1_4_1,⟨patch_mem1_1_4_2,⟨patch_mem1_1_4_4,⟨patch_mem1_1_4_7,⟨patch_mem1_1_4_9,⟨patch_mem1_1_4_10,by simp⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
