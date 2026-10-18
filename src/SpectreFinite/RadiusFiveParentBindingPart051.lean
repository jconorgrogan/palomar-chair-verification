module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock8T0C0
public import SpectreFinite.RadiusFivePruningLiteralBlock8T0C1
public import SpectreFinite.RadiusFivePruningLiteralBlock8T0C2
public import SpectreFinite.RadiusFivePruningLiteralBlock8T0C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq8_0_0_1 : RadiusFivePruning.stateRow8_0_0_1 = ParentOwnership.parentRow0765 := by rfl
theorem patch_mem8_0_0_1 : RadiusFivePruning.patch8_0_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0765, parentRow_mem0765, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0765_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_0_1]
  rfl
theorem row_eq8_0_0_3 : RadiusFivePruning.stateRow8_0_0_3 = ParentOwnership.parentRow0791 := by rfl
theorem patch_mem8_0_0_3 : RadiusFivePruning.patch8_0_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0791, parentRow_mem0791, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0791_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_0_3]
  rfl
theorem row_eq8_0_0_4 : RadiusFivePruning.stateRow8_0_0_4 = ParentOwnership.parentRow2002 := by rfl
theorem patch_mem8_0_0_4 : RadiusFivePruning.patch8_0_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2002, parentRow_mem2002, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2002_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_0_4]
  rfl
theorem row_eq8_0_0_5 : RadiusFivePruning.stateRow8_0_0_5 = ParentOwnership.parentRow2005 := by rfl
theorem patch_mem8_0_0_5 : RadiusFivePruning.patch8_0_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2005, parentRow_mem2005, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2005_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_0_5]
  rfl
theorem row_eq8_0_0_6 : RadiusFivePruning.stateRow8_0_0_6 = ParentOwnership.parentRow2008 := by rfl
theorem patch_mem8_0_0_6 : RadiusFivePruning.patch8_0_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2008, parentRow_mem2008, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2008_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_0_6]
  rfl
theorem row_eq8_0_0_7 : RadiusFivePruning.stateRow8_0_0_7 = ParentOwnership.parentRow2011 := by rfl
theorem patch_mem8_0_0_7 : RadiusFivePruning.patch8_0_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2011, parentRow_mem2011, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2011_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_0_7]
  rfl
theorem row_eq8_0_0_8 : RadiusFivePruning.stateRow8_0_0_8 = ParentOwnership.parentRow2012 := by rfl
theorem patch_mem8_0_0_8 : RadiusFivePruning.patch8_0_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2012, parentRow_mem2012, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2012_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_0_8]
  rfl
theorem row_eq8_0_0_9 : RadiusFivePruning.stateRow8_0_0_9 = ParentOwnership.parentRow2013 := by rfl
theorem patch_mem8_0_0_9 : RadiusFivePruning.patch8_0_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2013, parentRow_mem2013, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2013_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_0_9]
  rfl
theorem row_eq8_0_0_10 : RadiusFivePruning.stateRow8_0_0_10 = ParentOwnership.parentRow2018 := by rfl
theorem patch_mem8_0_0_10 : RadiusFivePruning.patch8_0_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2018, parentRow_mem2018, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2018_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_0_10]
  rfl
theorem row_eq8_0_0_11 : RadiusFivePruning.stateRow8_0_0_11 = ParentOwnership.parentRow2019 := by rfl
theorem patch_mem8_0_0_11 : RadiusFivePruning.patch8_0_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2019, parentRow_mem2019, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2019_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_0_11]
  rfl
theorem chunk_mem8_0_0 : ∀ p ∈ RadiusFivePruning.final8_0_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_0_0, List.forall_mem_cons]
  exact ⟨patch_mem8_0_0_1,⟨patch_mem8_0_0_3,⟨patch_mem8_0_0_4,⟨patch_mem8_0_0_5,⟨patch_mem8_0_0_6,⟨patch_mem8_0_0_7,⟨patch_mem8_0_0_8,⟨patch_mem8_0_0_9,⟨patch_mem8_0_0_10,⟨patch_mem8_0_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_0_1_0 : RadiusFivePruning.stateRow8_0_1_0 = ParentOwnership.parentRow2020 := by rfl
theorem patch_mem8_0_1_0 : RadiusFivePruning.patch8_0_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2020, parentRow_mem2020, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2020_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_1_0]
  rfl
theorem row_eq8_0_1_1 : RadiusFivePruning.stateRow8_0_1_1 = ParentOwnership.parentRow2021 := by rfl
theorem patch_mem8_0_1_1 : RadiusFivePruning.patch8_0_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2021, parentRow_mem2021, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2021_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_1_1]
  rfl
theorem row_eq8_0_1_2 : RadiusFivePruning.stateRow8_0_1_2 = ParentOwnership.parentRow2022 := by rfl
theorem patch_mem8_0_1_2 : RadiusFivePruning.patch8_0_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2022, parentRow_mem2022, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2022_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_1_2]
  rfl
theorem row_eq8_0_1_3 : RadiusFivePruning.stateRow8_0_1_3 = ParentOwnership.parentRow2023 := by rfl
theorem patch_mem8_0_1_3 : RadiusFivePruning.patch8_0_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2023, parentRow_mem2023, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2023_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_1_3]
  rfl
theorem row_eq8_0_1_4 : RadiusFivePruning.stateRow8_0_1_4 = ParentOwnership.parentRow2024 := by rfl
theorem patch_mem8_0_1_4 : RadiusFivePruning.patch8_0_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2024, parentRow_mem2024, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2024_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_1_4]
  rfl
theorem row_eq8_0_1_6 : RadiusFivePruning.stateRow8_0_1_6 = ParentOwnership.parentRow2042 := by rfl
theorem patch_mem8_0_1_6 : RadiusFivePruning.patch8_0_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2042, parentRow_mem2042, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2042_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_1_6]
  rfl
theorem row_eq8_0_1_8 : RadiusFivePruning.stateRow8_0_1_8 = ParentOwnership.parentRow2043 := by rfl
theorem patch_mem8_0_1_8 : RadiusFivePruning.patch8_0_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2043, parentRow_mem2043, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2043_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_1_8]
  rfl
theorem row_eq8_0_1_9 : RadiusFivePruning.stateRow8_0_1_9 = ParentOwnership.parentRow2044 := by rfl
theorem patch_mem8_0_1_9 : RadiusFivePruning.patch8_0_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2044, parentRow_mem2044, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2044_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_1_9]
  rfl
theorem row_eq8_0_1_10 : RadiusFivePruning.stateRow8_0_1_10 = ParentOwnership.parentRow2045 := by rfl
theorem patch_mem8_0_1_10 : RadiusFivePruning.patch8_0_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2045, parentRow_mem2045, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2045_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_1_10]
  rfl
theorem chunk_mem8_0_1 : ∀ p ∈ RadiusFivePruning.final8_0_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_0_1, List.forall_mem_cons]
  exact ⟨patch_mem8_0_1_0,⟨patch_mem8_0_1_1,⟨patch_mem8_0_1_2,⟨patch_mem8_0_1_3,⟨patch_mem8_0_1_4,⟨patch_mem8_0_1_6,⟨patch_mem8_0_1_8,⟨patch_mem8_0_1_9,⟨patch_mem8_0_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_0_2_0 : RadiusFivePruning.stateRow8_0_2_0 = ParentOwnership.parentRow2046 := by rfl
theorem patch_mem8_0_2_0 : RadiusFivePruning.patch8_0_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2046, parentRow_mem2046, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2046_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_2_0]
  rfl
theorem row_eq8_0_2_2 : RadiusFivePruning.stateRow8_0_2_2 = ParentOwnership.parentRow2048 := by rfl
theorem patch_mem8_0_2_2 : RadiusFivePruning.patch8_0_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2048, parentRow_mem2048, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2048_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_2_2]
  rfl
theorem row_eq8_0_2_3 : RadiusFivePruning.stateRow8_0_2_3 = ParentOwnership.parentRow2049 := by rfl
theorem patch_mem8_0_2_3 : RadiusFivePruning.patch8_0_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2049, parentRow_mem2049, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2049_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_2_3]
  rfl
theorem row_eq8_0_2_4 : RadiusFivePruning.stateRow8_0_2_4 = ParentOwnership.parentRow2050 := by rfl
theorem patch_mem8_0_2_4 : RadiusFivePruning.patch8_0_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2050, parentRow_mem2050, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2050_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_2_4]
  rfl
theorem row_eq8_0_2_5 : RadiusFivePruning.stateRow8_0_2_5 = ParentOwnership.parentRow2051 := by rfl
theorem patch_mem8_0_2_5 : RadiusFivePruning.patch8_0_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2051, parentRow_mem2051, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2051_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_2_5]
  rfl
theorem row_eq8_0_2_6 : RadiusFivePruning.stateRow8_0_2_6 = ParentOwnership.parentRow0052 := by rfl
theorem patch_mem8_0_2_6 : RadiusFivePruning.patch8_0_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0052, parentRow_mem0052, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0052_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_2_6]
  rfl
theorem row_eq8_0_2_7 : RadiusFivePruning.stateRow8_0_2_7 = ParentOwnership.parentRow0055 := by rfl
theorem patch_mem8_0_2_7 : RadiusFivePruning.patch8_0_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0055, parentRow_mem0055, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0055_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_2_7]
  rfl
theorem row_eq8_0_2_8 : RadiusFivePruning.stateRow8_0_2_8 = ParentOwnership.parentRow0496 := by rfl
theorem patch_mem8_0_2_8 : RadiusFivePruning.patch8_0_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0496, parentRow_mem0496, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0496_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_2_8]
  rfl
theorem row_eq8_0_2_9 : RadiusFivePruning.stateRow8_0_2_9 = ParentOwnership.parentRow0497 := by rfl
theorem patch_mem8_0_2_9 : RadiusFivePruning.patch8_0_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0497, parentRow_mem0497, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0497_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_2_9]
  rfl
theorem row_eq8_0_2_10 : RadiusFivePruning.stateRow8_0_2_10 = ParentOwnership.parentRow0498 := by rfl
theorem patch_mem8_0_2_10 : RadiusFivePruning.patch8_0_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0498, parentRow_mem0498, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0498_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_2_10]
  rfl
theorem row_eq8_0_2_11 : RadiusFivePruning.stateRow8_0_2_11 = ParentOwnership.parentRow0499 := by rfl
theorem patch_mem8_0_2_11 : RadiusFivePruning.patch8_0_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0499, parentRow_mem0499, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0499_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_2_11]
  rfl
theorem chunk_mem8_0_2 : ∀ p ∈ RadiusFivePruning.final8_0_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_0_2, List.forall_mem_cons]
  exact ⟨patch_mem8_0_2_0,⟨patch_mem8_0_2_2,⟨patch_mem8_0_2_3,⟨patch_mem8_0_2_4,⟨patch_mem8_0_2_5,⟨patch_mem8_0_2_6,⟨patch_mem8_0_2_7,⟨patch_mem8_0_2_8,⟨patch_mem8_0_2_9,⟨patch_mem8_0_2_10,⟨patch_mem8_0_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_0_3_0 : RadiusFivePruning.stateRow8_0_3_0 = ParentOwnership.parentRow2009 := by rfl
theorem patch_mem8_0_3_0 : RadiusFivePruning.patch8_0_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2009, parentRow_mem2009, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2009_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_3_0]
  rfl
theorem row_eq8_0_3_1 : RadiusFivePruning.stateRow8_0_3_1 = ParentOwnership.parentRow2010 := by rfl
theorem patch_mem8_0_3_1 : RadiusFivePruning.patch8_0_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2010, parentRow_mem2010, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2010_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_3_1]
  rfl
theorem row_eq8_0_3_3 : RadiusFivePruning.stateRow8_0_3_3 = ParentOwnership.parentRow2014 := by rfl
theorem patch_mem8_0_3_3 : RadiusFivePruning.patch8_0_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2014, parentRow_mem2014, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2014_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_3_3]
  rfl
theorem row_eq8_0_3_4 : RadiusFivePruning.stateRow8_0_3_4 = ParentOwnership.parentRow2015 := by rfl
theorem patch_mem8_0_3_4 : RadiusFivePruning.patch8_0_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2015, parentRow_mem2015, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2015_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_3_4]
  rfl
theorem row_eq8_0_3_5 : RadiusFivePruning.stateRow8_0_3_5 = ParentOwnership.parentRow2016 := by rfl
theorem patch_mem8_0_3_5 : RadiusFivePruning.patch8_0_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2016, parentRow_mem2016, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2016_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_3_5]
  rfl
theorem row_eq8_0_3_6 : RadiusFivePruning.stateRow8_0_3_6 = ParentOwnership.parentRow2017 := by rfl
theorem patch_mem8_0_3_6 : RadiusFivePruning.patch8_0_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2017, parentRow_mem2017, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2017_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_3_6]
  rfl
theorem row_eq8_0_3_7 : RadiusFivePruning.stateRow8_0_3_7 = ParentOwnership.parentRow0606 := by rfl
theorem patch_mem8_0_3_7 : RadiusFivePruning.patch8_0_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0606, parentRow_mem0606, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0606_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_3_7]
  rfl
theorem row_eq8_0_3_8 : RadiusFivePruning.stateRow8_0_3_8 = ParentOwnership.parentRow0607 := by rfl
theorem patch_mem8_0_3_8 : RadiusFivePruning.patch8_0_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0607, parentRow_mem0607, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0607_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_3_8]
  rfl
theorem row_eq8_0_3_9 : RadiusFivePruning.stateRow8_0_3_9 = ParentOwnership.parentRow0609 := by rfl
theorem patch_mem8_0_3_9 : RadiusFivePruning.patch8_0_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0609, parentRow_mem0609, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0609_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_3_9]
  rfl
theorem row_eq8_0_3_10 : RadiusFivePruning.stateRow8_0_3_10 = ParentOwnership.parentRow0610 := by rfl
theorem patch_mem8_0_3_10 : RadiusFivePruning.patch8_0_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0610, parentRow_mem0610, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0610_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_3_10]
  rfl
theorem row_eq8_0_3_11 : RadiusFivePruning.stateRow8_0_3_11 = ParentOwnership.parentRow0611 := by rfl
theorem patch_mem8_0_3_11 : RadiusFivePruning.patch8_0_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0611, parentRow_mem0611, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0611_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_3_11]
  rfl
theorem chunk_mem8_0_3 : ∀ p ∈ RadiusFivePruning.final8_0_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_0_3, List.forall_mem_cons]
  exact ⟨patch_mem8_0_3_0,⟨patch_mem8_0_3_1,⟨patch_mem8_0_3_3,⟨patch_mem8_0_3_4,⟨patch_mem8_0_3_5,⟨patch_mem8_0_3_6,⟨patch_mem8_0_3_7,⟨patch_mem8_0_3_8,⟨patch_mem8_0_3_9,⟨patch_mem8_0_3_10,⟨patch_mem8_0_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
