module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock0T2C2
public import SpectreFinite.RadiusFivePruningLiteralBlock0T2C3
public import SpectreFinite.RadiusFivePruningLiteralBlock0T2C4
public import SpectreFinite.RadiusFivePruningLiteralBlock0T3C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq0_2_2_0 : RadiusFivePruning.stateRow0_2_2_0 = ParentOwnership.parentRow1903 := by rfl
theorem patch_mem0_2_2_0 : RadiusFivePruning.patch0_2_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1903, parentRow_mem1903, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1903_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_2_0]
  rfl
theorem row_eq0_2_2_1 : RadiusFivePruning.stateRow0_2_2_1 = ParentOwnership.parentRow0883 := by rfl
theorem patch_mem0_2_2_1 : RadiusFivePruning.patch0_2_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0883, parentRow_mem0883, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0883_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_2_1]
  rfl
theorem row_eq0_2_2_2 : RadiusFivePruning.stateRow0_2_2_2 = ParentOwnership.parentRow1897 := by rfl
theorem patch_mem0_2_2_2 : RadiusFivePruning.patch0_2_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1897, parentRow_mem1897, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1897_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_2_2]
  rfl
theorem row_eq0_2_2_3 : RadiusFivePruning.stateRow0_2_2_3 = ParentOwnership.parentRow1902 := by rfl
theorem patch_mem0_2_2_3 : RadiusFivePruning.patch0_2_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1902, parentRow_mem1902, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1902_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_2_3]
  rfl
theorem row_eq0_2_2_5 : RadiusFivePruning.stateRow0_2_2_5 = ParentOwnership.parentRow1901 := by rfl
theorem patch_mem0_2_2_5 : RadiusFivePruning.patch0_2_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1901, parentRow_mem1901, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1901_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_2_5]
  rfl
theorem row_eq0_2_2_6 : RadiusFivePruning.stateRow0_2_2_6 = ParentOwnership.parentRow1915 := by rfl
theorem patch_mem0_2_2_6 : RadiusFivePruning.patch0_2_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1915, parentRow_mem1915, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1915_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_2_6]
  rfl
theorem row_eq0_2_2_7 : RadiusFivePruning.stateRow0_2_2_7 = ParentOwnership.parentRow0880 := by rfl
theorem patch_mem0_2_2_7 : RadiusFivePruning.patch0_2_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0880, parentRow_mem0880, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0880_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_2_7]
  rfl
theorem row_eq0_2_2_8 : RadiusFivePruning.stateRow0_2_2_8 = ParentOwnership.parentRow1894 := by rfl
theorem patch_mem0_2_2_8 : RadiusFivePruning.patch0_2_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1894, parentRow_mem1894, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1894_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_2_8]
  rfl
theorem row_eq0_2_2_9 : RadiusFivePruning.stateRow0_2_2_9 = ParentOwnership.parentRow1900 := by rfl
theorem patch_mem0_2_2_9 : RadiusFivePruning.patch0_2_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1900, parentRow_mem1900, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1900_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_2_9]
  rfl
theorem row_eq0_2_2_10 : RadiusFivePruning.stateRow0_2_2_10 = ParentOwnership.parentRow1914 := by rfl
theorem patch_mem0_2_2_10 : RadiusFivePruning.patch0_2_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1914, parentRow_mem1914, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1914_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_2_10]
  rfl
theorem chunk_mem0_2_2 : ∀ p ∈ RadiusFivePruning.final0_2_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_2_2, List.forall_mem_cons]
  exact ⟨patch_mem0_2_2_0,⟨patch_mem0_2_2_1,⟨patch_mem0_2_2_2,⟨patch_mem0_2_2_3,⟨patch_mem0_2_2_5,⟨patch_mem0_2_2_6,⟨patch_mem0_2_2_7,⟨patch_mem0_2_2_8,⟨patch_mem0_2_2_9,⟨patch_mem0_2_2_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_2_3_0 : RadiusFivePruning.stateRow0_2_3_0 = ParentOwnership.parentRow1916 := by rfl
theorem patch_mem0_2_3_0 : RadiusFivePruning.patch0_2_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1916, parentRow_mem1916, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1916_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_3_0]
  rfl
theorem row_eq0_2_3_2 : RadiusFivePruning.stateRow0_2_3_2 = ParentOwnership.parentRow1934 := by rfl
theorem patch_mem0_2_3_2 : RadiusFivePruning.patch0_2_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1934, parentRow_mem1934, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1934_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_3_2]
  rfl
theorem row_eq0_2_3_3 : RadiusFivePruning.stateRow0_2_3_3 = ParentOwnership.parentRow0889 := by rfl
theorem patch_mem0_2_3_3 : RadiusFivePruning.patch0_2_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0889, parentRow_mem0889, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0889_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_3_3]
  rfl
theorem row_eq0_2_3_4 : RadiusFivePruning.stateRow0_2_3_4 = ParentOwnership.parentRow1946 := by rfl
theorem patch_mem0_2_3_4 : RadiusFivePruning.patch0_2_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1946, parentRow_mem1946, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1946_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_3_4]
  rfl
theorem row_eq0_2_3_5 : RadiusFivePruning.stateRow0_2_3_5 = ParentOwnership.parentRow1935 := by rfl
theorem patch_mem0_2_3_5 : RadiusFivePruning.patch0_2_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1935, parentRow_mem1935, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1935_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_3_5]
  rfl
theorem row_eq0_2_3_6 : RadiusFivePruning.stateRow0_2_3_6 = ParentOwnership.parentRow1006 := by rfl
theorem patch_mem0_2_3_6 : RadiusFivePruning.patch0_2_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1006, parentRow_mem1006, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1006_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_3_6]
  rfl
theorem row_eq0_2_3_8 : RadiusFivePruning.stateRow0_2_3_8 = ParentOwnership.parentRow1919 := by rfl
theorem patch_mem0_2_3_8 : RadiusFivePruning.patch0_2_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1919, parentRow_mem1919, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1919_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_3_8]
  rfl
theorem row_eq0_2_3_9 : RadiusFivePruning.stateRow0_2_3_9 = ParentOwnership.parentRow0884 := by rfl
theorem patch_mem0_2_3_9 : RadiusFivePruning.patch0_2_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0884, parentRow_mem0884, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0884_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_3_9]
  rfl
theorem row_eq0_2_3_11 : RadiusFivePruning.stateRow0_2_3_11 = ParentOwnership.parentRow1904 := by rfl
theorem patch_mem0_2_3_11 : RadiusFivePruning.patch0_2_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1904, parentRow_mem1904, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1904_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_3_11]
  rfl
theorem chunk_mem0_2_3 : ∀ p ∈ RadiusFivePruning.final0_2_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_2_3, List.forall_mem_cons]
  exact ⟨patch_mem0_2_3_0,⟨patch_mem0_2_3_2,⟨patch_mem0_2_3_3,⟨patch_mem0_2_3_4,⟨patch_mem0_2_3_5,⟨patch_mem0_2_3_6,⟨patch_mem0_2_3_8,⟨patch_mem0_2_3_9,⟨patch_mem0_2_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_2_4_0 : RadiusFivePruning.stateRow0_2_4_0 = ParentOwnership.parentRow1917 := by rfl
theorem patch_mem0_2_4_0 : RadiusFivePruning.patch0_2_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1917, parentRow_mem1917, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1917_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_4_0]
  rfl
theorem row_eq0_2_4_1 : RadiusFivePruning.stateRow0_2_4_1 = ParentOwnership.parentRow1905 := by rfl
theorem patch_mem0_2_4_1 : RadiusFivePruning.patch0_2_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1905, parentRow_mem1905, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1905_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_4_1]
  rfl
theorem row_eq0_2_4_2 : RadiusFivePruning.stateRow0_2_4_2 = ParentOwnership.parentRow1918 := by rfl
theorem patch_mem0_2_4_2 : RadiusFivePruning.patch0_2_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1918, parentRow_mem1918, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1918_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_4_2]
  rfl
theorem row_eq0_2_4_4 : RadiusFivePruning.stateRow0_2_4_4 = ParentOwnership.parentRow1001 := by rfl
theorem patch_mem0_2_4_4 : RadiusFivePruning.patch0_2_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1001, parentRow_mem1001, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1001_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_4_4]
  rfl
theorem row_eq0_2_4_6 : RadiusFivePruning.stateRow0_2_4_6 = ParentOwnership.parentRow1936 := by rfl
theorem patch_mem0_2_4_6 : RadiusFivePruning.patch0_2_4_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1936, parentRow_mem1936, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1936_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_4_6]
  rfl
theorem row_eq0_2_4_7 : RadiusFivePruning.stateRow0_2_4_7 = ParentOwnership.parentRow1932 := by rfl
theorem patch_mem0_2_4_7 : RadiusFivePruning.patch0_2_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1932, parentRow_mem1932, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1932_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_4_7]
  rfl
theorem row_eq0_2_4_8 : RadiusFivePruning.stateRow0_2_4_8 = ParentOwnership.parentRow0888 := by rfl
theorem patch_mem0_2_4_8 : RadiusFivePruning.patch0_2_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0888, parentRow_mem0888, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0888_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_4_8]
  rfl
theorem row_eq0_2_4_9 : RadiusFivePruning.stateRow0_2_4_9 = ParentOwnership.parentRow1945 := by rfl
theorem patch_mem0_2_4_9 : RadiusFivePruning.patch0_2_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1945, parentRow_mem1945, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1945_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_4_9]
  rfl
theorem row_eq0_2_4_10 : RadiusFivePruning.stateRow0_2_4_10 = ParentOwnership.parentRow1933 := by rfl
theorem patch_mem0_2_4_10 : RadiusFivePruning.patch0_2_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1933, parentRow_mem1933, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1933_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_2_4_10]
  rfl
theorem chunk_mem0_2_4 : ∀ p ∈ RadiusFivePruning.final0_2_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_2_4, List.forall_mem_cons]
  exact ⟨patch_mem0_2_4_0,⟨patch_mem0_2_4_1,⟨patch_mem0_2_4_2,⟨patch_mem0_2_4_4,⟨patch_mem0_2_4_6,⟨patch_mem0_2_4_7,⟨patch_mem0_2_4_8,⟨patch_mem0_2_4_9,⟨patch_mem0_2_4_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq0_3_0_0 : RadiusFivePruning.stateRow0_3_0_0 = ParentOwnership.parentRow0627 := by rfl
theorem patch_mem0_3_0_0 : RadiusFivePruning.patch0_3_0_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0627, parentRow_mem0627, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0627_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_0_0]
  rfl
theorem row_eq0_3_0_1 : RadiusFivePruning.stateRow0_3_0_1 = ParentOwnership.parentRow0639 := by rfl
theorem patch_mem0_3_0_1 : RadiusFivePruning.patch0_3_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0639, parentRow_mem0639, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0639_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_0_1]
  rfl
theorem row_eq0_3_0_3 : RadiusFivePruning.stateRow0_3_0_3 = ParentOwnership.parentRow0631 := by rfl
theorem patch_mem0_3_0_3 : RadiusFivePruning.patch0_3_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0631, parentRow_mem0631, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0631_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_0_3]
  rfl
theorem row_eq0_3_0_4 : RadiusFivePruning.stateRow0_3_0_4 = ParentOwnership.parentRow0643 := by rfl
theorem patch_mem0_3_0_4 : RadiusFivePruning.patch0_3_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0643, parentRow_mem0643, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0643_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_0_4]
  rfl
theorem row_eq0_3_0_5 : RadiusFivePruning.stateRow0_3_0_5 = ParentOwnership.parentRow0640 := by rfl
theorem patch_mem0_3_0_5 : RadiusFivePruning.patch0_3_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0640, parentRow_mem0640, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0640_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_0_5]
  rfl
theorem row_eq0_3_0_6 : RadiusFivePruning.stateRow0_3_0_6 = ParentOwnership.parentRow0629 := by rfl
theorem patch_mem0_3_0_6 : RadiusFivePruning.patch0_3_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0629, parentRow_mem0629, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0629_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_0_6]
  rfl
theorem row_eq0_3_0_8 : RadiusFivePruning.stateRow0_3_0_8 = ParentOwnership.parentRow1814 := by rfl
theorem patch_mem0_3_0_8 : RadiusFivePruning.patch0_3_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1814, parentRow_mem1814, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1814_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_0_8]
  rfl
theorem row_eq0_3_0_9 : RadiusFivePruning.stateRow0_3_0_9 = ParentOwnership.parentRow0628 := by rfl
theorem patch_mem0_3_0_9 : RadiusFivePruning.patch0_3_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0628, parentRow_mem0628, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0628_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_0_9]
  rfl
theorem row_eq0_3_0_10 : RadiusFivePruning.stateRow0_3_0_10 = ParentOwnership.parentRow0632 := by rfl
theorem patch_mem0_3_0_10 : RadiusFivePruning.patch0_3_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0632, parentRow_mem0632, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0632_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_0_10]
  rfl
theorem row_eq0_3_0_11 : RadiusFivePruning.stateRow0_3_0_11 = ParentOwnership.parentRow0644 := by rfl
theorem patch_mem0_3_0_11 : RadiusFivePruning.patch0_3_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0644, parentRow_mem0644, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0644_property.1, ← literalDomain_eq_hexRegion, ← row_eq0_3_0_11]
  rfl
theorem chunk_mem0_3_0 : ∀ p ∈ RadiusFivePruning.final0_3_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final0_3_0, List.forall_mem_cons]
  exact ⟨patch_mem0_3_0_0,⟨patch_mem0_3_0_1,⟨patch_mem0_3_0_3,⟨patch_mem0_3_0_4,⟨patch_mem0_3_0_5,⟨patch_mem0_3_0_6,⟨patch_mem0_3_0_8,⟨patch_mem0_3_0_9,⟨patch_mem0_3_0_10,⟨patch_mem0_3_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
