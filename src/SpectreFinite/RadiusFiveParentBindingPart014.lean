module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock1T5C1
public import SpectreFinite.RadiusFivePruningLiteralBlock1T5C2
public import SpectreFinite.RadiusFivePruningLiteralBlock1T5C3
public import SpectreFinite.RadiusFivePruningLiteralBlock1T5C4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq1_5_1_1 : RadiusFivePruning.stateRow1_5_1_1 = ParentOwnership.parentRow1016 := by rfl
theorem patch_mem1_5_1_1 : RadiusFivePruning.patch1_5_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1016, parentRow_mem1016, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1016_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_1_1]
  rfl
theorem row_eq1_5_1_2 : RadiusFivePruning.stateRow1_5_1_2 = ParentOwnership.parentRow1017 := by rfl
theorem patch_mem1_5_1_2 : RadiusFivePruning.patch1_5_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1017, parentRow_mem1017, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1017_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_1_2]
  rfl
theorem row_eq1_5_1_3 : RadiusFivePruning.stateRow1_5_1_3 = ParentOwnership.parentRow1018 := by rfl
theorem patch_mem1_5_1_3 : RadiusFivePruning.patch1_5_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1018, parentRow_mem1018, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1018_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_1_3]
  rfl
theorem row_eq1_5_1_4 : RadiusFivePruning.stateRow1_5_1_4 = ParentOwnership.parentRow1019 := by rfl
theorem patch_mem1_5_1_4 : RadiusFivePruning.patch1_5_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1019, parentRow_mem1019, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1019_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_1_4]
  rfl
theorem row_eq1_5_1_5 : RadiusFivePruning.stateRow1_5_1_5 = ParentOwnership.parentRow2083 := by rfl
theorem patch_mem1_5_1_5 : RadiusFivePruning.patch1_5_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2083, parentRow_mem2083, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2083_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_1_5]
  rfl
theorem row_eq1_5_1_6 : RadiusFivePruning.stateRow1_5_1_6 = ParentOwnership.parentRow2085 := by rfl
theorem patch_mem1_5_1_6 : RadiusFivePruning.patch1_5_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2085, parentRow_mem2085, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2085_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_1_6]
  rfl
theorem row_eq1_5_1_8 : RadiusFivePruning.stateRow1_5_1_8 = ParentOwnership.parentRow2086 := by rfl
theorem patch_mem1_5_1_8 : RadiusFivePruning.patch1_5_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2086, parentRow_mem2086, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2086_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_1_8]
  rfl
theorem row_eq1_5_1_9 : RadiusFivePruning.stateRow1_5_1_9 = ParentOwnership.parentRow2087 := by rfl
theorem patch_mem1_5_1_9 : RadiusFivePruning.patch1_5_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2087, parentRow_mem2087, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2087_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_1_9]
  rfl
theorem row_eq1_5_1_10 : RadiusFivePruning.stateRow1_5_1_10 = ParentOwnership.parentRow2084 := by rfl
theorem patch_mem1_5_1_10 : RadiusFivePruning.patch1_5_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2084, parentRow_mem2084, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2084_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_1_10]
  rfl
theorem chunk_mem1_5_1 : ∀ p ∈ RadiusFivePruning.final1_5_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_5_1, List.forall_mem_cons]
  exact ⟨patch_mem1_5_1_1,⟨patch_mem1_5_1_2,⟨patch_mem1_5_1_3,⟨patch_mem1_5_1_4,⟨patch_mem1_5_1_5,⟨patch_mem1_5_1_6,⟨patch_mem1_5_1_8,⟨patch_mem1_5_1_9,⟨patch_mem1_5_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_5_2_0 : RadiusFivePruning.stateRow1_5_2_0 = ParentOwnership.parentRow2069 := by rfl
theorem patch_mem1_5_2_0 : RadiusFivePruning.patch1_5_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2069, parentRow_mem2069, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2069_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_2_0]
  rfl
theorem row_eq1_5_2_1 : RadiusFivePruning.stateRow1_5_2_1 = ParentOwnership.parentRow0798 := by rfl
theorem patch_mem1_5_2_1 : RadiusFivePruning.patch1_5_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0798, parentRow_mem0798, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0798_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_2_1]
  rfl
theorem row_eq1_5_2_2 : RadiusFivePruning.stateRow1_5_2_2 = ParentOwnership.parentRow2070 := by rfl
theorem patch_mem1_5_2_2 : RadiusFivePruning.patch1_5_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2070, parentRow_mem2070, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2070_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_2_2]
  rfl
theorem row_eq1_5_2_3 : RadiusFivePruning.stateRow1_5_2_3 = ParentOwnership.parentRow2071 := by rfl
theorem patch_mem1_5_2_3 : RadiusFivePruning.patch1_5_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2071, parentRow_mem2071, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2071_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_2_3]
  rfl
theorem row_eq1_5_2_4 : RadiusFivePruning.stateRow1_5_2_4 = ParentOwnership.parentRow2068 := by rfl
theorem patch_mem1_5_2_4 : RadiusFivePruning.patch1_5_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2068, parentRow_mem2068, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2068_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_2_4]
  rfl
theorem row_eq1_5_2_6 : RadiusFivePruning.stateRow1_5_2_6 = ParentOwnership.parentRow1021 := by rfl
theorem patch_mem1_5_2_6 : RadiusFivePruning.patch1_5_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1021, parentRow_mem1021, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1021_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_2_6]
  rfl
theorem row_eq1_5_2_7 : RadiusFivePruning.stateRow1_5_2_7 = ParentOwnership.parentRow1022 := by rfl
theorem patch_mem1_5_2_7 : RadiusFivePruning.patch1_5_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1022, parentRow_mem1022, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1022_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_2_7]
  rfl
theorem row_eq1_5_2_8 : RadiusFivePruning.stateRow1_5_2_8 = ParentOwnership.parentRow1023 := by rfl
theorem patch_mem1_5_2_8 : RadiusFivePruning.patch1_5_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1023, parentRow_mem1023, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1023_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_2_8]
  rfl
theorem row_eq1_5_2_9 : RadiusFivePruning.stateRow1_5_2_9 = ParentOwnership.parentRow1025 := by rfl
theorem patch_mem1_5_2_9 : RadiusFivePruning.patch1_5_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1025, parentRow_mem1025, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1025_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_2_9]
  rfl
theorem row_eq1_5_2_11 : RadiusFivePruning.stateRow1_5_2_11 = ParentOwnership.parentRow1024 := by rfl
theorem patch_mem1_5_2_11 : RadiusFivePruning.patch1_5_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1024, parentRow_mem1024, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1024_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_2_11]
  rfl
theorem chunk_mem1_5_2 : ∀ p ∈ RadiusFivePruning.final1_5_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_5_2, List.forall_mem_cons]
  exact ⟨patch_mem1_5_2_0,⟨patch_mem1_5_2_1,⟨patch_mem1_5_2_2,⟨patch_mem1_5_2_3,⟨patch_mem1_5_2_4,⟨patch_mem1_5_2_6,⟨patch_mem1_5_2_7,⟨patch_mem1_5_2_8,⟨patch_mem1_5_2_9,⟨patch_mem1_5_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_5_3_0 : RadiusFivePruning.stateRow1_5_3_0 = ParentOwnership.parentRow1026 := by rfl
theorem patch_mem1_5_3_0 : RadiusFivePruning.patch1_5_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1026, parentRow_mem1026, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1026_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_3_0]
  rfl
theorem row_eq1_5_3_1 : RadiusFivePruning.stateRow1_5_3_1 = ParentOwnership.parentRow1020 := by rfl
theorem patch_mem1_5_3_1 : RadiusFivePruning.patch1_5_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1020, parentRow_mem1020, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1020_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_3_1]
  rfl
theorem row_eq1_5_3_3 : RadiusFivePruning.stateRow1_5_3_3 = ParentOwnership.parentRow0892 := by rfl
theorem patch_mem1_5_3_3 : RadiusFivePruning.patch1_5_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0892, parentRow_mem0892, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0892_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_3_3]
  rfl
theorem row_eq1_5_3_5 : RadiusFivePruning.stateRow1_5_3_5 = ParentOwnership.parentRow0893 := by rfl
theorem patch_mem1_5_3_5 : RadiusFivePruning.patch1_5_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0893, parentRow_mem0893, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0893_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_3_5]
  rfl
theorem row_eq1_5_3_6 : RadiusFivePruning.stateRow1_5_3_6 = ParentOwnership.parentRow0890 := by rfl
theorem patch_mem1_5_3_6 : RadiusFivePruning.patch1_5_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0890, parentRow_mem0890, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0890_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_3_6]
  rfl
theorem row_eq1_5_3_7 : RadiusFivePruning.stateRow1_5_3_7 = ParentOwnership.parentRow1027 := by rfl
theorem patch_mem1_5_3_7 : RadiusFivePruning.patch1_5_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1027, parentRow_mem1027, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1027_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_3_7]
  rfl
theorem row_eq1_5_3_8 : RadiusFivePruning.stateRow1_5_3_8 = ParentOwnership.parentRow0894 := by rfl
theorem patch_mem1_5_3_8 : RadiusFivePruning.patch1_5_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0894, parentRow_mem0894, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0894_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_3_8]
  rfl
theorem row_eq1_5_3_9 : RadiusFivePruning.stateRow1_5_3_9 = ParentOwnership.parentRow0891 := by rfl
theorem patch_mem1_5_3_9 : RadiusFivePruning.patch1_5_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0891, parentRow_mem0891, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0891_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_3_9]
  rfl
theorem row_eq1_5_3_10 : RadiusFivePruning.stateRow1_5_3_10 = ParentOwnership.parentRow0895 := by rfl
theorem patch_mem1_5_3_10 : RadiusFivePruning.patch1_5_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0895, parentRow_mem0895, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0895_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_3_10]
  rfl
theorem row_eq1_5_3_11 : RadiusFivePruning.stateRow1_5_3_11 = ParentOwnership.parentRow0897 := by rfl
theorem patch_mem1_5_3_11 : RadiusFivePruning.patch1_5_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0897, parentRow_mem0897, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0897_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_3_11]
  rfl
theorem chunk_mem1_5_3 : ∀ p ∈ RadiusFivePruning.final1_5_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_5_3, List.forall_mem_cons]
  exact ⟨patch_mem1_5_3_0,⟨patch_mem1_5_3_1,⟨patch_mem1_5_3_3,⟨patch_mem1_5_3_5,⟨patch_mem1_5_3_6,⟨patch_mem1_5_3_7,⟨patch_mem1_5_3_8,⟨patch_mem1_5_3_9,⟨patch_mem1_5_3_10,⟨patch_mem1_5_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_5_4_1 : RadiusFivePruning.stateRow1_5_4_1 = ParentOwnership.parentRow0898 := by rfl
theorem patch_mem1_5_4_1 : RadiusFivePruning.patch1_5_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0898, parentRow_mem0898, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0898_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_4_1]
  rfl
theorem row_eq1_5_4_2 : RadiusFivePruning.stateRow1_5_4_2 = ParentOwnership.parentRow0896 := by rfl
theorem patch_mem1_5_4_2 : RadiusFivePruning.patch1_5_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0896, parentRow_mem0896, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0896_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_4_2]
  rfl
theorem row_eq1_5_4_4 : RadiusFivePruning.stateRow1_5_4_4 = ParentOwnership.parentRow0594 := by rfl
theorem patch_mem1_5_4_4 : RadiusFivePruning.patch1_5_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0594, parentRow_mem0594, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0594_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_4_4]
  rfl
theorem row_eq1_5_4_7 : RadiusFivePruning.stateRow1_5_4_7 = ParentOwnership.parentRow1463 := by rfl
theorem patch_mem1_5_4_7 : RadiusFivePruning.patch1_5_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1463, parentRow_mem1463, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1463_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_4_7]
  rfl
theorem row_eq1_5_4_9 : RadiusFivePruning.stateRow1_5_4_9 = ParentOwnership.parentRow1464 := by rfl
theorem patch_mem1_5_4_9 : RadiusFivePruning.patch1_5_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1464, parentRow_mem1464, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1464_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_4_9]
  rfl
theorem row_eq1_5_4_10 : RadiusFivePruning.stateRow1_5_4_10 = ParentOwnership.parentRow1465 := by rfl
theorem patch_mem1_5_4_10 : RadiusFivePruning.patch1_5_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1465, parentRow_mem1465, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1465_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_5_4_10]
  rfl
theorem chunk_mem1_5_4 : ∀ p ∈ RadiusFivePruning.final1_5_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_5_4, List.forall_mem_cons]
  exact ⟨patch_mem1_5_4_1,⟨patch_mem1_5_4_2,⟨patch_mem1_5_4_4,⟨patch_mem1_5_4_7,⟨patch_mem1_5_4_9,⟨patch_mem1_5_4_10,by simp⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
