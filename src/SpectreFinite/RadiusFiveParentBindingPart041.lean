module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock7T1C5
public import SpectreFinite.RadiusFivePruningLiteralBlock7T1C6
public import SpectreFinite.RadiusFivePruningLiteralBlock7T1C7
public import SpectreFinite.RadiusFivePruningLiteralBlock7T1C8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq7_1_5_0 : RadiusFivePruning.stateRow7_1_5_0 = ParentOwnership.parentRow1787 := by rfl
theorem patch_mem7_1_5_0 : RadiusFivePruning.patch7_1_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1787, parentRow_mem1787, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1787_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_5_0]
  rfl
theorem row_eq7_1_5_2 : RadiusFivePruning.stateRow7_1_5_2 = ParentOwnership.parentRow1794 := by rfl
theorem patch_mem7_1_5_2 : RadiusFivePruning.patch7_1_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1794, parentRow_mem1794, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1794_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_5_2]
  rfl
theorem row_eq7_1_5_3 : RadiusFivePruning.stateRow7_1_5_3 = ParentOwnership.parentRow1796 := by rfl
theorem patch_mem7_1_5_3 : RadiusFivePruning.patch7_1_5_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1796, parentRow_mem1796, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1796_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_5_3]
  rfl
theorem row_eq7_1_5_4 : RadiusFivePruning.stateRow7_1_5_4 = ParentOwnership.parentRow0921 := by rfl
theorem patch_mem7_1_5_4 : RadiusFivePruning.patch7_1_5_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0921, parentRow_mem0921, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0921_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_5_4]
  rfl
theorem row_eq7_1_5_5 : RadiusFivePruning.stateRow7_1_5_5 = ParentOwnership.parentRow0931 := by rfl
theorem patch_mem7_1_5_5 : RadiusFivePruning.patch7_1_5_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0931, parentRow_mem0931, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0931_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_5_5]
  rfl
theorem row_eq7_1_5_6 : RadiusFivePruning.stateRow7_1_5_6 = ParentOwnership.parentRow0928 := by rfl
theorem patch_mem7_1_5_6 : RadiusFivePruning.patch7_1_5_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0928, parentRow_mem0928, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0928_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_5_6]
  rfl
theorem row_eq7_1_5_7 : RadiusFivePruning.stateRow7_1_5_7 = ParentOwnership.parentRow0932 := by rfl
theorem patch_mem7_1_5_7 : RadiusFivePruning.patch7_1_5_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0932, parentRow_mem0932, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0932_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_5_7]
  rfl
theorem row_eq7_1_5_8 : RadiusFivePruning.stateRow7_1_5_8 = ParentOwnership.parentRow0939 := by rfl
theorem patch_mem7_1_5_8 : RadiusFivePruning.patch7_1_5_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0939, parentRow_mem0939, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0939_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_5_8]
  rfl
theorem row_eq7_1_5_9 : RadiusFivePruning.stateRow7_1_5_9 = ParentOwnership.parentRow0943 := by rfl
theorem patch_mem7_1_5_9 : RadiusFivePruning.patch7_1_5_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0943, parentRow_mem0943, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0943_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_5_9]
  rfl
theorem row_eq7_1_5_10 : RadiusFivePruning.stateRow7_1_5_10 = ParentOwnership.parentRow0940 := by rfl
theorem patch_mem7_1_5_10 : RadiusFivePruning.patch7_1_5_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0940, parentRow_mem0940, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0940_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_5_10]
  rfl
theorem row_eq7_1_5_11 : RadiusFivePruning.stateRow7_1_5_11 = ParentOwnership.parentRow1987 := by rfl
theorem patch_mem7_1_5_11 : RadiusFivePruning.patch7_1_5_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1987, parentRow_mem1987, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1987_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_5_11]
  rfl
theorem chunk_mem7_1_5 : ∀ p ∈ RadiusFivePruning.final7_1_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_1_5, List.forall_mem_cons]
  exact ⟨patch_mem7_1_5_0,⟨patch_mem7_1_5_2,⟨patch_mem7_1_5_3,⟨patch_mem7_1_5_4,⟨patch_mem7_1_5_5,⟨patch_mem7_1_5_6,⟨patch_mem7_1_5_7,⟨patch_mem7_1_5_8,⟨patch_mem7_1_5_9,⟨patch_mem7_1_5_10,⟨patch_mem7_1_5_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_1_6_0 : RadiusFivePruning.stateRow7_1_6_0 = ParentOwnership.parentRow1995 := by rfl
theorem patch_mem7_1_6_0 : RadiusFivePruning.patch7_1_6_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1995, parentRow_mem1995, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1995_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_6_0]
  rfl
theorem row_eq7_1_6_1 : RadiusFivePruning.stateRow7_1_6_1 = ParentOwnership.parentRow1992 := by rfl
theorem patch_mem7_1_6_1 : RadiusFivePruning.patch7_1_6_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1992, parentRow_mem1992, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1992_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_6_1]
  rfl
theorem row_eq7_1_6_2 : RadiusFivePruning.stateRow7_1_6_2 = ParentOwnership.parentRow1996 := by rfl
theorem patch_mem7_1_6_2 : RadiusFivePruning.patch7_1_6_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1996, parentRow_mem1996, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1996_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_6_2]
  rfl
theorem row_eq7_1_6_4 : RadiusFivePruning.stateRow7_1_6_4 = ParentOwnership.parentRow0927 := by rfl
theorem patch_mem7_1_6_4 : RadiusFivePruning.patch7_1_6_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0927, parentRow_mem0927, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0927_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_6_4]
  rfl
theorem row_eq7_1_6_6 : RadiusFivePruning.stateRow7_1_6_6 = ParentOwnership.parentRow0930 := by rfl
theorem patch_mem7_1_6_6 : RadiusFivePruning.patch7_1_6_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0930, parentRow_mem0930, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0930_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_6_6]
  rfl
theorem row_eq7_1_6_7 : RadiusFivePruning.stateRow7_1_6_7 = ParentOwnership.parentRow0929 := by rfl
theorem patch_mem7_1_6_7 : RadiusFivePruning.patch7_1_6_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0929, parentRow_mem0929, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0929_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_6_7]
  rfl
theorem row_eq7_1_6_9 : RadiusFivePruning.stateRow7_1_6_9 = ParentOwnership.parentRow0937 := by rfl
theorem patch_mem7_1_6_9 : RadiusFivePruning.patch7_1_6_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0937, parentRow_mem0937, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0937_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_6_9]
  rfl
theorem row_eq7_1_6_10 : RadiusFivePruning.stateRow7_1_6_10 = ParentOwnership.parentRow0938 := by rfl
theorem patch_mem7_1_6_10 : RadiusFivePruning.patch7_1_6_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0938, parentRow_mem0938, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0938_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_6_10]
  rfl
theorem row_eq7_1_6_11 : RadiusFivePruning.stateRow7_1_6_11 = ParentOwnership.parentRow0941 := by rfl
theorem patch_mem7_1_6_11 : RadiusFivePruning.patch7_1_6_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0941, parentRow_mem0941, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0941_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_6_11]
  rfl
theorem chunk_mem7_1_6 : ∀ p ∈ RadiusFivePruning.final7_1_6, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_1_6, List.forall_mem_cons]
  exact ⟨patch_mem7_1_6_0,⟨patch_mem7_1_6_1,⟨patch_mem7_1_6_2,⟨patch_mem7_1_6_4,⟨patch_mem7_1_6_6,⟨patch_mem7_1_6_7,⟨patch_mem7_1_6_9,⟨patch_mem7_1_6_10,⟨patch_mem7_1_6_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_1_7_0 : RadiusFivePruning.stateRow7_1_7_0 = ParentOwnership.parentRow0942 := by rfl
theorem patch_mem7_1_7_0 : RadiusFivePruning.patch7_1_7_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0942, parentRow_mem0942, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0942_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_7_0]
  rfl
theorem row_eq7_1_7_1 : RadiusFivePruning.stateRow7_1_7_1 = ParentOwnership.parentRow1988 := by rfl
theorem patch_mem7_1_7_1 : RadiusFivePruning.patch7_1_7_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1988, parentRow_mem1988, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1988_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_7_1]
  rfl
theorem row_eq7_1_7_2 : RadiusFivePruning.stateRow7_1_7_2 = ParentOwnership.parentRow1989 := by rfl
theorem patch_mem7_1_7_2 : RadiusFivePruning.patch7_1_7_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1989, parentRow_mem1989, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1989_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_7_2]
  rfl
theorem row_eq7_1_7_3 : RadiusFivePruning.stateRow7_1_7_3 = ParentOwnership.parentRow1993 := by rfl
theorem patch_mem7_1_7_3 : RadiusFivePruning.patch7_1_7_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1993, parentRow_mem1993, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1993_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_7_3]
  rfl
theorem row_eq7_1_7_4 : RadiusFivePruning.stateRow7_1_7_4 = ParentOwnership.parentRow1994 := by rfl
theorem patch_mem7_1_7_4 : RadiusFivePruning.patch7_1_7_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1994, parentRow_mem1994, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1994_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_7_4]
  rfl
theorem row_eq7_1_7_5 : RadiusFivePruning.stateRow7_1_7_5 = ParentOwnership.parentRow0918 := by rfl
theorem patch_mem7_1_7_5 : RadiusFivePruning.patch7_1_7_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0918, parentRow_mem0918, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0918_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_7_5]
  rfl
theorem row_eq7_1_7_6 : RadiusFivePruning.stateRow7_1_7_6 = ParentOwnership.parentRow0823 := by rfl
theorem patch_mem7_1_7_6 : RadiusFivePruning.patch7_1_7_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0823, parentRow_mem0823, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0823_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_7_6]
  rfl
theorem row_eq7_1_7_11 : RadiusFivePruning.stateRow7_1_7_11 = ParentOwnership.parentRow0831 := by rfl
theorem patch_mem7_1_7_11 : RadiusFivePruning.patch7_1_7_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0831, parentRow_mem0831, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0831_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_7_11]
  rfl
theorem chunk_mem7_1_7 : ∀ p ∈ RadiusFivePruning.final7_1_7, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_1_7, List.forall_mem_cons]
  exact ⟨patch_mem7_1_7_0,⟨patch_mem7_1_7_1,⟨patch_mem7_1_7_2,⟨patch_mem7_1_7_3,⟨patch_mem7_1_7_4,⟨patch_mem7_1_7_5,⟨patch_mem7_1_7_6,⟨patch_mem7_1_7_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_1_8_0 : RadiusFivePruning.stateRow7_1_8_0 = ParentOwnership.parentRow0832 := by rfl
theorem patch_mem7_1_8_0 : RadiusFivePruning.patch7_1_8_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0832, parentRow_mem0832, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0832_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_8_0]
  rfl
theorem row_eq7_1_8_1 : RadiusFivePruning.stateRow7_1_8_1 = ParentOwnership.parentRow0840 := by rfl
theorem patch_mem7_1_8_1 : RadiusFivePruning.patch7_1_8_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0840, parentRow_mem0840, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0840_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_8_1]
  rfl
theorem row_eq7_1_8_2 : RadiusFivePruning.stateRow7_1_8_2 = ParentOwnership.parentRow0845 := by rfl
theorem patch_mem7_1_8_2 : RadiusFivePruning.patch7_1_8_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0845, parentRow_mem0845, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0845_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_8_2]
  rfl
theorem row_eq7_1_8_3 : RadiusFivePruning.stateRow7_1_8_3 = ParentOwnership.parentRow0841 := by rfl
theorem patch_mem7_1_8_3 : RadiusFivePruning.patch7_1_8_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0841, parentRow_mem0841, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0841_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_8_3]
  rfl
theorem row_eq7_1_8_5 : RadiusFivePruning.stateRow7_1_8_5 = ParentOwnership.parentRow1982 := by rfl
theorem patch_mem7_1_8_5 : RadiusFivePruning.patch7_1_8_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1982, parentRow_mem1982, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1982_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_8_5]
  rfl
theorem row_eq7_1_8_7 : RadiusFivePruning.stateRow7_1_8_7 = ParentOwnership.parentRow1981 := by rfl
theorem patch_mem7_1_8_7 : RadiusFivePruning.patch7_1_8_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1981, parentRow_mem1981, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1981_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_8_7]
  rfl
theorem row_eq7_1_8_8 : RadiusFivePruning.stateRow7_1_8_8 = ParentOwnership.parentRow1983 := by rfl
theorem patch_mem7_1_8_8 : RadiusFivePruning.patch7_1_8_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1983, parentRow_mem1983, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1983_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_8_8]
  rfl
theorem row_eq7_1_8_9 : RadiusFivePruning.stateRow7_1_8_9 = ParentOwnership.parentRow1984 := by rfl
theorem patch_mem7_1_8_9 : RadiusFivePruning.patch7_1_8_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1984, parentRow_mem1984, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1984_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_8_9]
  rfl
theorem chunk_mem7_1_8 : ∀ p ∈ RadiusFivePruning.final7_1_8, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_1_8, List.forall_mem_cons]
  exact ⟨patch_mem7_1_8_0,⟨patch_mem7_1_8_1,⟨patch_mem7_1_8_2,⟨patch_mem7_1_8_3,⟨patch_mem7_1_8_5,⟨patch_mem7_1_8_7,⟨patch_mem7_1_8_8,⟨patch_mem7_1_8_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
