module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock4T3C0
public import SpectreFinite.RadiusFivePruningLiteralBlock4T3C1
public import SpectreFinite.RadiusFivePruningLiteralBlock4T3C2
public import SpectreFinite.RadiusFivePruningLiteralBlock4T3C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq4_3_0_1 : RadiusFivePruning.stateRow4_3_0_1 = ParentOwnership.parentRow1208 := by rfl
theorem patch_mem4_3_0_1 : RadiusFivePruning.patch4_3_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1208, parentRow_mem1208, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1208_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_0_1]
  rfl
theorem row_eq4_3_0_3 : RadiusFivePruning.stateRow4_3_0_3 = ParentOwnership.parentRow1207 := by rfl
theorem patch_mem4_3_0_3 : RadiusFivePruning.patch4_3_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1207, parentRow_mem1207, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1207_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_0_3]
  rfl
theorem row_eq4_3_0_4 : RadiusFivePruning.stateRow4_3_0_4 = ParentOwnership.parentRow0009 := by rfl
theorem patch_mem4_3_0_4 : RadiusFivePruning.patch4_3_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0009, parentRow_mem0009, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0009_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_0_4]
  rfl
theorem row_eq4_3_0_6 : RadiusFivePruning.stateRow4_3_0_6 = ParentOwnership.parentRow0004 := by rfl
theorem patch_mem4_3_0_6 : RadiusFivePruning.patch4_3_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0004, parentRow_mem0004, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0004_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_0_6]
  rfl
theorem row_eq4_3_0_7 : RadiusFivePruning.stateRow4_3_0_7 = ParentOwnership.parentRow0011 := by rfl
theorem patch_mem4_3_0_7 : RadiusFivePruning.patch4_3_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0011, parentRow_mem0011, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0011_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_0_7]
  rfl
theorem row_eq4_3_0_9 : RadiusFivePruning.stateRow4_3_0_9 = ParentOwnership.parentRow0006 := by rfl
theorem patch_mem4_3_0_9 : RadiusFivePruning.patch4_3_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0006, parentRow_mem0006, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0006_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_0_9]
  rfl
theorem row_eq4_3_0_10 : RadiusFivePruning.stateRow4_3_0_10 = ParentOwnership.parentRow0013 := by rfl
theorem patch_mem4_3_0_10 : RadiusFivePruning.patch4_3_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0013, parentRow_mem0013, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0013_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_0_10]
  rfl
theorem row_eq4_3_0_11 : RadiusFivePruning.stateRow4_3_0_11 = ParentOwnership.parentRow0434 := by rfl
theorem patch_mem4_3_0_11 : RadiusFivePruning.patch4_3_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0434, parentRow_mem0434, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0434_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_0_11]
  rfl
theorem chunk_mem4_3_0 : ∀ p ∈ RadiusFivePruning.final4_3_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_3_0, List.forall_mem_cons]
  exact ⟨patch_mem4_3_0_1,⟨patch_mem4_3_0_3,⟨patch_mem4_3_0_4,⟨patch_mem4_3_0_6,⟨patch_mem4_3_0_7,⟨patch_mem4_3_0_9,⟨patch_mem4_3_0_10,⟨patch_mem4_3_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_3_1_0 : RadiusFivePruning.stateRow4_3_1_0 = ParentOwnership.parentRow0000 := by rfl
theorem patch_mem4_3_1_0 : RadiusFivePruning.patch4_3_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0000, parentRow_mem0000, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0000_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_1_0]
  rfl
theorem row_eq4_3_1_1 : RadiusFivePruning.stateRow4_3_1_1 = ParentOwnership.parentRow0008 := by rfl
theorem patch_mem4_3_1_1 : RadiusFivePruning.patch4_3_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0008, parentRow_mem0008, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0008_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_1_1]
  rfl
theorem row_eq4_3_1_3 : RadiusFivePruning.stateRow4_3_1_3 = ParentOwnership.parentRow0429 := by rfl
theorem patch_mem4_3_1_3 : RadiusFivePruning.patch4_3_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0429, parentRow_mem0429, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0429_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_1_3]
  rfl
theorem row_eq4_3_1_4 : RadiusFivePruning.stateRow4_3_1_4 = ParentOwnership.parentRow0010 := by rfl
theorem patch_mem4_3_1_4 : RadiusFivePruning.patch4_3_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0010, parentRow_mem0010, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0010_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_1_4]
  rfl
theorem row_eq4_3_1_5 : RadiusFivePruning.stateRow4_3_1_5 = ParentOwnership.parentRow1206 := by rfl
theorem patch_mem4_3_1_5 : RadiusFivePruning.patch4_3_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1206, parentRow_mem1206, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1206_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_1_5]
  rfl
theorem row_eq4_3_1_6 : RadiusFivePruning.stateRow4_3_1_6 = ParentOwnership.parentRow0015 := by rfl
theorem patch_mem4_3_1_6 : RadiusFivePruning.patch4_3_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0015, parentRow_mem0015, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0015_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_1_6]
  rfl
theorem row_eq4_3_1_7 : RadiusFivePruning.stateRow4_3_1_7 = ParentOwnership.parentRow0005 := by rfl
theorem patch_mem4_3_1_7 : RadiusFivePruning.patch4_3_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0005, parentRow_mem0005, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0005_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_1_7]
  rfl
theorem row_eq4_3_1_8 : RadiusFivePruning.stateRow4_3_1_8 = ParentOwnership.parentRow0012 := by rfl
theorem patch_mem4_3_1_8 : RadiusFivePruning.patch4_3_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0012, parentRow_mem0012, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0012_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_1_8]
  rfl
theorem row_eq4_3_1_10 : RadiusFivePruning.stateRow4_3_1_10 = ParentOwnership.parentRow0016 := by rfl
theorem patch_mem4_3_1_10 : RadiusFivePruning.patch4_3_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0016, parentRow_mem0016, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0016_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_1_10]
  rfl
theorem chunk_mem4_3_1 : ∀ p ∈ RadiusFivePruning.final4_3_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_3_1, List.forall_mem_cons]
  exact ⟨patch_mem4_3_1_0,⟨patch_mem4_3_1_1,⟨patch_mem4_3_1_3,⟨patch_mem4_3_1_4,⟨patch_mem4_3_1_5,⟨patch_mem4_3_1_6,⟨patch_mem4_3_1_7,⟨patch_mem4_3_1_8,⟨patch_mem4_3_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_3_2_0 : RadiusFivePruning.stateRow4_3_2_0 = ParentOwnership.parentRow1772 := by rfl
theorem patch_mem4_3_2_0 : RadiusFivePruning.patch4_3_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1772, parentRow_mem1772, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1772_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_2_0]
  rfl
theorem row_eq4_3_2_1 : RadiusFivePruning.stateRow4_3_2_1 = ParentOwnership.parentRow1773 := by rfl
theorem patch_mem4_3_2_1 : RadiusFivePruning.patch4_3_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1773, parentRow_mem1773, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1773_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_2_1]
  rfl
theorem row_eq4_3_2_2 : RadiusFivePruning.stateRow4_3_2_2 = ParentOwnership.parentRow1771 := by rfl
theorem patch_mem4_3_2_2 : RadiusFivePruning.patch4_3_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1771, parentRow_mem1771, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1771_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_2_2]
  rfl
theorem row_eq4_3_2_4 : RadiusFivePruning.stateRow4_3_2_4 = ParentOwnership.parentRow1774 := by rfl
theorem patch_mem4_3_2_4 : RadiusFivePruning.patch4_3_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1774, parentRow_mem1774, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1774_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_2_4]
  rfl
theorem row_eq4_3_2_6 : RadiusFivePruning.stateRow4_3_2_6 = ParentOwnership.parentRow1202 := by rfl
theorem patch_mem4_3_2_6 : RadiusFivePruning.patch4_3_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1202, parentRow_mem1202, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1202_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_2_6]
  rfl
theorem row_eq4_3_2_7 : RadiusFivePruning.stateRow4_3_2_7 = ParentOwnership.parentRow1203 := by rfl
theorem patch_mem4_3_2_7 : RadiusFivePruning.patch4_3_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1203, parentRow_mem1203, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1203_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_2_7]
  rfl
theorem row_eq4_3_2_9 : RadiusFivePruning.stateRow4_3_2_9 = ParentOwnership.parentRow0433 := by rfl
theorem patch_mem4_3_2_9 : RadiusFivePruning.patch4_3_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0433, parentRow_mem0433, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0433_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_2_9]
  rfl
theorem row_eq4_3_2_10 : RadiusFivePruning.stateRow4_3_2_10 = ParentOwnership.parentRow0001 := by rfl
theorem patch_mem4_3_2_10 : RadiusFivePruning.patch4_3_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0001, parentRow_mem0001, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0001_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_2_10]
  rfl
theorem row_eq4_3_2_11 : RadiusFivePruning.stateRow4_3_2_11 = ParentOwnership.parentRow0430 := by rfl
theorem patch_mem4_3_2_11 : RadiusFivePruning.patch4_3_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0430, parentRow_mem0430, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0430_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_2_11]
  rfl
theorem chunk_mem4_3_2 : ∀ p ∈ RadiusFivePruning.final4_3_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_3_2, List.forall_mem_cons]
  exact ⟨patch_mem4_3_2_0,⟨patch_mem4_3_2_1,⟨patch_mem4_3_2_2,⟨patch_mem4_3_2_4,⟨patch_mem4_3_2_6,⟨patch_mem4_3_2_7,⟨patch_mem4_3_2_9,⟨patch_mem4_3_2_10,⟨patch_mem4_3_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_3_3_0 : RadiusFivePruning.stateRow4_3_3_0 = ParentOwnership.parentRow0003 := by rfl
theorem patch_mem4_3_3_0 : RadiusFivePruning.patch4_3_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0003, parentRow_mem0003, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0003_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_3_0]
  rfl
theorem row_eq4_3_3_1 : RadiusFivePruning.stateRow4_3_3_1 = ParentOwnership.parentRow0432 := by rfl
theorem patch_mem4_3_3_1 : RadiusFivePruning.patch4_3_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0432, parentRow_mem0432, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0432_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_3_1]
  rfl
theorem row_eq4_3_3_2 : RadiusFivePruning.stateRow4_3_3_2 = ParentOwnership.parentRow1769 := by rfl
theorem patch_mem4_3_3_2 : RadiusFivePruning.patch4_3_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1769, parentRow_mem1769, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1769_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_3_2]
  rfl
theorem row_eq4_3_3_3 : RadiusFivePruning.stateRow4_3_3_3 = ParentOwnership.parentRow1204 := by rfl
theorem patch_mem4_3_3_3 : RadiusFivePruning.patch4_3_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1204, parentRow_mem1204, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1204_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_3_3]
  rfl
theorem row_eq4_3_3_4 : RadiusFivePruning.stateRow4_3_3_4 = ParentOwnership.parentRow1205 := by rfl
theorem patch_mem4_3_3_4 : RadiusFivePruning.patch4_3_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1205, parentRow_mem1205, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1205_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_3_4]
  rfl
theorem row_eq4_3_3_6 : RadiusFivePruning.stateRow4_3_3_6 = ParentOwnership.parentRow0002 := by rfl
theorem patch_mem4_3_3_6 : RadiusFivePruning.patch4_3_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0002, parentRow_mem0002, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0002_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_3_6]
  rfl
theorem row_eq4_3_3_7 : RadiusFivePruning.stateRow4_3_3_7 = ParentOwnership.parentRow0431 := by rfl
theorem patch_mem4_3_3_7 : RadiusFivePruning.patch4_3_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0431, parentRow_mem0431, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0431_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_3_7]
  rfl
theorem row_eq4_3_3_9 : RadiusFivePruning.stateRow4_3_3_9 = ParentOwnership.parentRow1770 := by rfl
theorem patch_mem4_3_3_9 : RadiusFivePruning.patch4_3_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1770, parentRow_mem1770, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1770_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_3_3_9]
  rfl
theorem chunk_mem4_3_3 : ∀ p ∈ RadiusFivePruning.final4_3_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_3_3, List.forall_mem_cons]
  exact ⟨patch_mem4_3_3_0,⟨patch_mem4_3_3_1,⟨patch_mem4_3_3_2,⟨patch_mem4_3_3_3,⟨patch_mem4_3_3_4,⟨patch_mem4_3_3_6,⟨patch_mem4_3_3_7,⟨patch_mem4_3_3_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
