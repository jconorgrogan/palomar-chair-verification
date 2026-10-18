module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock3T2C0
public import SpectreFinite.RadiusFivePruningLiteralBlock3T3C0
public import SpectreFinite.RadiusFivePruningLiteralBlock3T4C0
public import SpectreFinite.RadiusFivePruningLiteralBlock3T5C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq3_2_0_1 : RadiusFivePruning.stateRow3_2_0_1 = ParentOwnership.parentRow1151 := by rfl
theorem patch_mem3_2_0_1 : RadiusFivePruning.patch3_2_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1151, parentRow_mem1151, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1151_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_2_0_1]
  rfl
theorem row_eq3_2_0_3 : RadiusFivePruning.stateRow3_2_0_3 = ParentOwnership.parentRow1142 := by rfl
theorem patch_mem3_2_0_3 : RadiusFivePruning.patch3_2_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1142, parentRow_mem1142, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1142_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_2_0_3]
  rfl
theorem row_eq3_2_0_4 : RadiusFivePruning.stateRow3_2_0_4 = ParentOwnership.parentRow1148 := by rfl
theorem patch_mem3_2_0_4 : RadiusFivePruning.patch3_2_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1148, parentRow_mem1148, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1148_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_2_0_4]
  rfl
theorem row_eq3_2_0_5 : RadiusFivePruning.stateRow3_2_0_5 = ParentOwnership.parentRow1150 := by rfl
theorem patch_mem3_2_0_5 : RadiusFivePruning.patch3_2_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1150, parentRow_mem1150, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1150_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_2_0_5]
  rfl
theorem row_eq3_2_0_6 : RadiusFivePruning.stateRow3_2_0_6 = ParentOwnership.parentRow1149 := by rfl
theorem patch_mem3_2_0_6 : RadiusFivePruning.patch3_2_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1149, parentRow_mem1149, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1149_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_2_0_6]
  rfl
theorem chunk_mem3_2_0 : ∀ p ∈ RadiusFivePruning.final3_2_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final3_2_0, List.forall_mem_cons]
  exact ⟨patch_mem3_2_0_1,⟨patch_mem3_2_0_3,⟨patch_mem3_2_0_4,⟨patch_mem3_2_0_5,⟨patch_mem3_2_0_6,by simp⟩⟩⟩⟩⟩
theorem row_eq3_3_0_1 : RadiusFivePruning.stateRow3_3_0_1 = ParentOwnership.parentRow0069 := by rfl
theorem patch_mem3_3_0_1 : RadiusFivePruning.patch3_3_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0069, parentRow_mem0069, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0069_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_3_0_1]
  rfl
theorem row_eq3_3_0_3 : RadiusFivePruning.stateRow3_3_0_3 = ParentOwnership.parentRow0502 := by rfl
theorem patch_mem3_3_0_3 : RadiusFivePruning.patch3_3_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0502, parentRow_mem0502, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0502_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_3_0_3]
  rfl
theorem row_eq3_3_0_4 : RadiusFivePruning.stateRow3_3_0_4 = ParentOwnership.parentRow0062 := by rfl
theorem patch_mem3_3_0_4 : RadiusFivePruning.patch3_3_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0062, parentRow_mem0062, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0062_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_3_0_4]
  rfl
theorem row_eq3_3_0_5 : RadiusFivePruning.stateRow3_3_0_5 = ParentOwnership.parentRow0068 := by rfl
theorem patch_mem3_3_0_5 : RadiusFivePruning.patch3_3_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0068, parentRow_mem0068, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0068_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_3_0_5]
  rfl
theorem row_eq3_3_0_6 : RadiusFivePruning.stateRow3_3_0_6 = ParentOwnership.parentRow0063 := by rfl
theorem patch_mem3_3_0_6 : RadiusFivePruning.patch3_3_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0063, parentRow_mem0063, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0063_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_3_0_6]
  rfl
theorem chunk_mem3_3_0 : ∀ p ∈ RadiusFivePruning.final3_3_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final3_3_0, List.forall_mem_cons]
  exact ⟨patch_mem3_3_0_1,⟨patch_mem3_3_0_3,⟨patch_mem3_3_0_4,⟨patch_mem3_3_0_5,⟨patch_mem3_3_0_6,by simp⟩⟩⟩⟩⟩
theorem row_eq3_4_0_1 : RadiusFivePruning.stateRow3_4_0_1 = ParentOwnership.parentRow2075 := by rfl
theorem patch_mem3_4_0_1 : RadiusFivePruning.patch3_4_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2075, parentRow_mem2075, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2075_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_4_0_1]
  rfl
theorem row_eq3_4_0_3 : RadiusFivePruning.stateRow3_4_0_3 = ParentOwnership.parentRow0654 := by rfl
theorem patch_mem3_4_0_3 : RadiusFivePruning.patch3_4_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0654, parentRow_mem0654, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0654_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_4_0_3]
  rfl
theorem row_eq3_4_0_4 : RadiusFivePruning.stateRow3_4_0_4 = ParentOwnership.parentRow1754 := by rfl
theorem patch_mem3_4_0_4 : RadiusFivePruning.patch3_4_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1754, parentRow_mem1754, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1754_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_4_0_4]
  rfl
theorem row_eq3_4_0_5 : RadiusFivePruning.stateRow3_4_0_5 = ParentOwnership.parentRow2074 := by rfl
theorem patch_mem3_4_0_5 : RadiusFivePruning.patch3_4_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2074, parentRow_mem2074, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2074_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_4_0_5]
  rfl
theorem row_eq3_4_0_6 : RadiusFivePruning.stateRow3_4_0_6 = ParentOwnership.parentRow1759 := by rfl
theorem patch_mem3_4_0_6 : RadiusFivePruning.patch3_4_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1759, parentRow_mem1759, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1759_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_4_0_6]
  rfl
theorem chunk_mem3_4_0 : ∀ p ∈ RadiusFivePruning.final3_4_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final3_4_0, List.forall_mem_cons]
  exact ⟨patch_mem3_4_0_1,⟨patch_mem3_4_0_3,⟨patch_mem3_4_0_4,⟨patch_mem3_4_0_5,⟨patch_mem3_4_0_6,by simp⟩⟩⟩⟩⟩
theorem row_eq3_5_0_1 : RadiusFivePruning.stateRow3_5_0_1 = ParentOwnership.parentRow1466 := by rfl
theorem patch_mem3_5_0_1 : RadiusFivePruning.patch3_5_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1466, parentRow_mem1466, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1466_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_5_0_1]
  rfl
theorem row_eq3_5_0_3 : RadiusFivePruning.stateRow3_5_0_3 = ParentOwnership.parentRow0369 := by rfl
theorem patch_mem3_5_0_3 : RadiusFivePruning.patch3_5_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0369, parentRow_mem0369, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0369_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_5_0_3]
  rfl
theorem row_eq3_5_0_4 : RadiusFivePruning.stateRow3_5_0_4 = ParentOwnership.parentRow0595 := by rfl
theorem patch_mem3_5_0_4 : RadiusFivePruning.patch3_5_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0595, parentRow_mem0595, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0595_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_5_0_4]
  rfl
theorem row_eq3_5_0_5 : RadiusFivePruning.stateRow3_5_0_5 = ParentOwnership.parentRow1467 := by rfl
theorem patch_mem3_5_0_5 : RadiusFivePruning.patch3_5_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1467, parentRow_mem1467, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1467_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_5_0_5]
  rfl
theorem row_eq3_5_0_6 : RadiusFivePruning.stateRow3_5_0_6 = ParentOwnership.parentRow1468 := by rfl
theorem patch_mem3_5_0_6 : RadiusFivePruning.patch3_5_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1468, parentRow_mem1468, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1468_property.1, ← literalDomain_eq_hexRegion, ← row_eq3_5_0_6]
  rfl
theorem chunk_mem3_5_0 : ∀ p ∈ RadiusFivePruning.final3_5_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final3_5_0, List.forall_mem_cons]
  exact ⟨patch_mem3_5_0_1,⟨patch_mem3_5_0_3,⟨patch_mem3_5_0_4,⟨patch_mem3_5_0_5,⟨patch_mem3_5_0_6,by simp⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
