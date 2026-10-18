module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock1T3C3
public import SpectreFinite.RadiusFivePruningLiteralBlock1T3C4
public import SpectreFinite.RadiusFivePruningLiteralBlock1T4C0
public import SpectreFinite.RadiusFivePruningLiteralBlock1T4C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq1_3_3_0 : RadiusFivePruning.stateRow1_3_3_0 = ParentOwnership.parentRow1254 := by rfl
theorem patch_mem1_3_3_0 : RadiusFivePruning.patch1_3_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1254, parentRow_mem1254, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1254_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_3_0]
  rfl
theorem row_eq1_3_3_1 : RadiusFivePruning.stateRow1_3_3_1 = ParentOwnership.parentRow1224 := by rfl
theorem patch_mem1_3_3_1 : RadiusFivePruning.patch1_3_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1224, parentRow_mem1224, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1224_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_3_1]
  rfl
theorem row_eq1_3_3_3 : RadiusFivePruning.stateRow1_3_3_3 = ParentOwnership.parentRow1256 := by rfl
theorem patch_mem1_3_3_3 : RadiusFivePruning.patch1_3_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1256, parentRow_mem1256, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1256_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_3_3]
  rfl
theorem row_eq1_3_3_5 : RadiusFivePruning.stateRow1_3_3_5 = ParentOwnership.parentRow0042 := by rfl
theorem patch_mem1_3_3_5 : RadiusFivePruning.patch1_3_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0042, parentRow_mem0042, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0042_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_3_5]
  rfl
theorem row_eq1_3_3_6 : RadiusFivePruning.stateRow1_3_3_6 = ParentOwnership.parentRow1222 := by rfl
theorem patch_mem1_3_3_6 : RadiusFivePruning.patch1_3_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1222, parentRow_mem1222, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1222_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_3_6]
  rfl
theorem row_eq1_3_3_7 : RadiusFivePruning.stateRow1_3_3_7 = ParentOwnership.parentRow1225 := by rfl
theorem patch_mem1_3_3_7 : RadiusFivePruning.patch1_3_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1225, parentRow_mem1225, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1225_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_3_7]
  rfl
theorem row_eq1_3_3_8 : RadiusFivePruning.stateRow1_3_3_8 = ParentOwnership.parentRow0041 := by rfl
theorem patch_mem1_3_3_8 : RadiusFivePruning.patch1_3_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0041, parentRow_mem0041, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0041_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_3_8]
  rfl
theorem row_eq1_3_3_9 : RadiusFivePruning.stateRow1_3_3_9 = ParentOwnership.parentRow1221 := by rfl
theorem patch_mem1_3_3_9 : RadiusFivePruning.patch1_3_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1221, parentRow_mem1221, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1221_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_3_9]
  rfl
theorem row_eq1_3_3_10 : RadiusFivePruning.stateRow1_3_3_10 = ParentOwnership.parentRow0059 := by rfl
theorem patch_mem1_3_3_10 : RadiusFivePruning.patch1_3_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0059, parentRow_mem0059, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0059_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_3_10]
  rfl
theorem row_eq1_3_3_11 : RadiusFivePruning.stateRow1_3_3_11 = ParentOwnership.parentRow1257 := by rfl
theorem patch_mem1_3_3_11 : RadiusFivePruning.patch1_3_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1257, parentRow_mem1257, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1257_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_3_11]
  rfl
theorem chunk_mem1_3_3 : ∀ p ∈ RadiusFivePruning.final1_3_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_3_3, List.forall_mem_cons]
  exact ⟨patch_mem1_3_3_0,⟨patch_mem1_3_3_1,⟨patch_mem1_3_3_3,⟨patch_mem1_3_3_5,⟨patch_mem1_3_3_6,⟨patch_mem1_3_3_7,⟨patch_mem1_3_3_8,⟨patch_mem1_3_3_9,⟨patch_mem1_3_3_10,⟨patch_mem1_3_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_3_4_1 : RadiusFivePruning.stateRow1_3_4_1 = ParentOwnership.parentRow0043 := by rfl
theorem patch_mem1_3_4_1 : RadiusFivePruning.patch1_3_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0043, parentRow_mem0043, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0043_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_4_1]
  rfl
theorem row_eq1_3_4_2 : RadiusFivePruning.stateRow1_3_4_2 = ParentOwnership.parentRow1223 := by rfl
theorem patch_mem1_3_4_2 : RadiusFivePruning.patch1_3_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1223, parentRow_mem1223, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1223_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_4_2]
  rfl
theorem row_eq1_3_4_4 : RadiusFivePruning.stateRow1_3_4_4 = ParentOwnership.parentRow0060 := by rfl
theorem patch_mem1_3_4_4 : RadiusFivePruning.patch1_3_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0060, parentRow_mem0060, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0060_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_4_4]
  rfl
theorem row_eq1_3_4_7 : RadiusFivePruning.stateRow1_3_4_7 = ParentOwnership.parentRow0067 := by rfl
theorem patch_mem1_3_4_7 : RadiusFivePruning.patch1_3_4_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0067, parentRow_mem0067, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0067_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_4_7]
  rfl
theorem row_eq1_3_4_9 : RadiusFivePruning.stateRow1_3_4_9 = ParentOwnership.parentRow0066 := by rfl
theorem patch_mem1_3_4_9 : RadiusFivePruning.patch1_3_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0066, parentRow_mem0066, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0066_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_4_9]
  rfl
theorem row_eq1_3_4_10 : RadiusFivePruning.stateRow1_3_4_10 = ParentOwnership.parentRow0061 := by rfl
theorem patch_mem1_3_4_10 : RadiusFivePruning.patch1_3_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0061, parentRow_mem0061, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0061_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_3_4_10]
  rfl
theorem chunk_mem1_3_4 : ∀ p ∈ RadiusFivePruning.final1_3_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_3_4, List.forall_mem_cons]
  exact ⟨patch_mem1_3_4_1,⟨patch_mem1_3_4_2,⟨patch_mem1_3_4_4,⟨patch_mem1_3_4_7,⟨patch_mem1_3_4_9,⟨patch_mem1_3_4_10,by simp⟩⟩⟩⟩⟩⟩
theorem row_eq1_4_0_1 : RadiusFivePruning.stateRow1_4_0_1 = ParentOwnership.parentRow1713 := by rfl
theorem patch_mem1_4_0_1 : RadiusFivePruning.patch1_4_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1713, parentRow_mem1713, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1713_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_0_1]
  rfl
theorem row_eq1_4_0_2 : RadiusFivePruning.stateRow1_4_0_2 = ParentOwnership.parentRow1690 := by rfl
theorem patch_mem1_4_0_2 : RadiusFivePruning.patch1_4_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1690, parentRow_mem1690, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1690_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_0_2]
  rfl
theorem row_eq1_4_0_3 : RadiusFivePruning.stateRow1_4_0_3 = ParentOwnership.parentRow0522 := by rfl
theorem patch_mem1_4_0_3 : RadiusFivePruning.patch1_4_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0522, parentRow_mem0522, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0522_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_0_3]
  rfl
theorem row_eq1_4_0_5 : RadiusFivePruning.stateRow1_4_0_5 = ParentOwnership.parentRow1720 := by rfl
theorem patch_mem1_4_0_5 : RadiusFivePruning.patch1_4_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1720, parentRow_mem1720, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1720_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_0_5]
  rfl
theorem row_eq1_4_0_6 : RadiusFivePruning.stateRow1_4_0_6 = ParentOwnership.parentRow0529 := by rfl
theorem patch_mem1_4_0_6 : RadiusFivePruning.patch1_4_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0529, parentRow_mem0529, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0529_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_0_6]
  rfl
theorem row_eq1_4_0_7 : RadiusFivePruning.stateRow1_4_0_7 = ParentOwnership.parentRow0531 := by rfl
theorem patch_mem1_4_0_7 : RadiusFivePruning.patch1_4_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0531, parentRow_mem0531, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0531_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_0_7]
  rfl
theorem row_eq1_4_0_8 : RadiusFivePruning.stateRow1_4_0_8 = ParentOwnership.parentRow0530 := by rfl
theorem patch_mem1_4_0_8 : RadiusFivePruning.patch1_4_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0530, parentRow_mem0530, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0530_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_0_8]
  rfl
theorem row_eq1_4_0_9 : RadiusFivePruning.stateRow1_4_0_9 = ParentOwnership.parentRow0532 := by rfl
theorem patch_mem1_4_0_9 : RadiusFivePruning.patch1_4_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0532, parentRow_mem0532, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0532_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_0_9]
  rfl
theorem row_eq1_4_0_10 : RadiusFivePruning.stateRow1_4_0_10 = ParentOwnership.parentRow1716 := by rfl
theorem patch_mem1_4_0_10 : RadiusFivePruning.patch1_4_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1716, parentRow_mem1716, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1716_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_0_10]
  rfl
theorem row_eq1_4_0_11 : RadiusFivePruning.stateRow1_4_0_11 = ParentOwnership.parentRow0535 := by rfl
theorem patch_mem1_4_0_11 : RadiusFivePruning.patch1_4_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0535, parentRow_mem0535, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0535_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_0_11]
  rfl
theorem chunk_mem1_4_0 : ∀ p ∈ RadiusFivePruning.final1_4_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_4_0, List.forall_mem_cons]
  exact ⟨patch_mem1_4_0_1,⟨patch_mem1_4_0_2,⟨patch_mem1_4_0_3,⟨patch_mem1_4_0_5,⟨patch_mem1_4_0_6,⟨patch_mem1_4_0_7,⟨patch_mem1_4_0_8,⟨patch_mem1_4_0_9,⟨patch_mem1_4_0_10,⟨patch_mem1_4_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq1_4_1_1 : RadiusFivePruning.stateRow1_4_1_1 = ParentOwnership.parentRow0543 := by rfl
theorem patch_mem1_4_1_1 : RadiusFivePruning.patch1_4_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0543, parentRow_mem0543, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0543_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_1_1]
  rfl
theorem row_eq1_4_1_2 : RadiusFivePruning.stateRow1_4_1_2 = ParentOwnership.parentRow0545 := by rfl
theorem patch_mem1_4_1_2 : RadiusFivePruning.patch1_4_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0545, parentRow_mem0545, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0545_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_1_2]
  rfl
theorem row_eq1_4_1_3 : RadiusFivePruning.stateRow1_4_1_3 = ParentOwnership.parentRow0544 := by rfl
theorem patch_mem1_4_1_3 : RadiusFivePruning.patch1_4_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0544, parentRow_mem0544, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0544_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_1_3]
  rfl
theorem row_eq1_4_1_4 : RadiusFivePruning.stateRow1_4_1_4 = ParentOwnership.parentRow0546 := by rfl
theorem patch_mem1_4_1_4 : RadiusFivePruning.patch1_4_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0546, parentRow_mem0546, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0546_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_1_4]
  rfl
theorem row_eq1_4_1_5 : RadiusFivePruning.stateRow1_4_1_5 = ParentOwnership.parentRow1683 := by rfl
theorem patch_mem1_4_1_5 : RadiusFivePruning.patch1_4_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1683, parentRow_mem1683, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1683_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_1_5]
  rfl
theorem row_eq1_4_1_6 : RadiusFivePruning.stateRow1_4_1_6 = ParentOwnership.parentRow0526 := by rfl
theorem patch_mem1_4_1_6 : RadiusFivePruning.patch1_4_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0526, parentRow_mem0526, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0526_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_1_6]
  rfl
theorem row_eq1_4_1_8 : RadiusFivePruning.stateRow1_4_1_8 = ParentOwnership.parentRow0527 := by rfl
theorem patch_mem1_4_1_8 : RadiusFivePruning.patch1_4_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0527, parentRow_mem0527, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0527_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_1_8]
  rfl
theorem row_eq1_4_1_9 : RadiusFivePruning.stateRow1_4_1_9 = ParentOwnership.parentRow0528 := by rfl
theorem patch_mem1_4_1_9 : RadiusFivePruning.patch1_4_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0528, parentRow_mem0528, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0528_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_1_9]
  rfl
theorem row_eq1_4_1_10 : RadiusFivePruning.stateRow1_4_1_10 = ParentOwnership.parentRow0517 := by rfl
theorem patch_mem1_4_1_10 : RadiusFivePruning.patch1_4_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0517, parentRow_mem0517, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0517_property.1, ← literalDomain_eq_hexRegion, ← row_eq1_4_1_10]
  rfl
theorem chunk_mem1_4_1 : ∀ p ∈ RadiusFivePruning.final1_4_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final1_4_1, List.forall_mem_cons]
  exact ⟨patch_mem1_4_1_1,⟨patch_mem1_4_1_2,⟨patch_mem1_4_1_3,⟨patch_mem1_4_1_4,⟨patch_mem1_4_1_5,⟨patch_mem1_4_1_6,⟨patch_mem1_4_1_8,⟨patch_mem1_4_1_9,⟨patch_mem1_4_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
