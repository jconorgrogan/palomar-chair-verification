module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock5T4C0
public import SpectreFinite.RadiusFivePruningLiteralBlock5T4C1
public import SpectreFinite.RadiusFivePruningLiteralBlock5T4C2
public import SpectreFinite.RadiusFivePruningLiteralBlock5T5C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq5_4_0_2 : RadiusFivePruning.stateRow5_4_0_2 = ParentOwnership.parentRow1427 := by rfl
theorem patch_mem5_4_0_2 : RadiusFivePruning.patch5_4_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1427, parentRow_mem1427, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1427_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_0_2]
  rfl
theorem row_eq5_4_0_3 : RadiusFivePruning.stateRow5_4_0_3 = ParentOwnership.parentRow1421 := by rfl
theorem patch_mem5_4_0_3 : RadiusFivePruning.patch5_4_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1421, parentRow_mem1421, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1421_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_0_3]
  rfl
theorem row_eq5_4_0_4 : RadiusFivePruning.stateRow5_4_0_4 = ParentOwnership.parentRow1417 := by rfl
theorem patch_mem5_4_0_4 : RadiusFivePruning.patch5_4_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1417, parentRow_mem1417, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1417_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_0_4]
  rfl
theorem row_eq5_4_0_6 : RadiusFivePruning.stateRow5_4_0_6 = ParentOwnership.parentRow1423 := by rfl
theorem patch_mem5_4_0_6 : RadiusFivePruning.patch5_4_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1423, parentRow_mem1423, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1423_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_0_6]
  rfl
theorem row_eq5_4_0_7 : RadiusFivePruning.stateRow5_4_0_7 = ParentOwnership.parentRow1422 := by rfl
theorem patch_mem5_4_0_7 : RadiusFivePruning.patch5_4_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1422, parentRow_mem1422, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1422_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_0_7]
  rfl
theorem row_eq5_4_0_9 : RadiusFivePruning.stateRow5_4_0_9 = ParentOwnership.parentRow0557 := by rfl
theorem patch_mem5_4_0_9 : RadiusFivePruning.patch5_4_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0557, parentRow_mem0557, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0557_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_0_9]
  rfl
theorem row_eq5_4_0_10 : RadiusFivePruning.stateRow5_4_0_10 = ParentOwnership.parentRow0801 := by rfl
theorem patch_mem5_4_0_10 : RadiusFivePruning.patch5_4_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0801, parentRow_mem0801, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0801_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_0_10]
  rfl
theorem row_eq5_4_0_11 : RadiusFivePruning.stateRow5_4_0_11 = ParentOwnership.parentRow0581 := by rfl
theorem patch_mem5_4_0_11 : RadiusFivePruning.patch5_4_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0581, parentRow_mem0581, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0581_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_0_11]
  rfl
theorem chunk_mem5_4_0 : ∀ p ∈ RadiusFivePruning.final5_4_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_4_0, List.forall_mem_cons]
  exact ⟨patch_mem5_4_0_2,⟨patch_mem5_4_0_3,⟨patch_mem5_4_0_4,⟨patch_mem5_4_0_6,⟨patch_mem5_4_0_7,⟨patch_mem5_4_0_9,⟨patch_mem5_4_0_10,⟨patch_mem5_4_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq5_4_1_0 : RadiusFivePruning.stateRow5_4_1_0 = ParentOwnership.parentRow0567 := by rfl
theorem patch_mem5_4_1_0 : RadiusFivePruning.patch5_4_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0567, parentRow_mem0567, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0567_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_1_0]
  rfl
theorem row_eq5_4_1_1 : RadiusFivePruning.stateRow5_4_1_1 = ParentOwnership.parentRow0665 := by rfl
theorem patch_mem5_4_1_1 : RadiusFivePruning.patch5_4_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0665, parentRow_mem0665, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0665_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_1_1]
  rfl
theorem row_eq5_4_1_3 : RadiusFivePruning.stateRow5_4_1_3 = ParentOwnership.parentRow0663 := by rfl
theorem patch_mem5_4_1_3 : RadiusFivePruning.patch5_4_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0663, parentRow_mem0663, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0663_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_1_3]
  rfl
theorem row_eq5_4_1_4 : RadiusFivePruning.stateRow5_4_1_4 = ParentOwnership.parentRow0556 := by rfl
theorem patch_mem5_4_1_4 : RadiusFivePruning.patch5_4_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0556, parentRow_mem0556, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0556_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_1_4]
  rfl
theorem row_eq5_4_1_7 : RadiusFivePruning.stateRow5_4_1_7 = ParentOwnership.parentRow0569 := by rfl
theorem patch_mem5_4_1_7 : RadiusFivePruning.patch5_4_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0569, parentRow_mem0569, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0569_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_1_7]
  rfl
theorem row_eq5_4_1_8 : RadiusFivePruning.stateRow5_4_1_8 = ParentOwnership.parentRow0558 := by rfl
theorem patch_mem5_4_1_8 : RadiusFivePruning.patch5_4_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0558, parentRow_mem0558, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0558_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_1_8]
  rfl
theorem row_eq5_4_1_9 : RadiusFivePruning.stateRow5_4_1_9 = ParentOwnership.parentRow0582 := by rfl
theorem patch_mem5_4_1_9 : RadiusFivePruning.patch5_4_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0582, parentRow_mem0582, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0582_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_1_9]
  rfl
theorem row_eq5_4_1_11 : RadiusFivePruning.stateRow5_4_1_11 = ParentOwnership.parentRow0568 := by rfl
theorem patch_mem5_4_1_11 : RadiusFivePruning.patch5_4_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0568, parentRow_mem0568, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0568_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_1_11]
  rfl
theorem chunk_mem5_4_1 : ∀ p ∈ RadiusFivePruning.final5_4_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_4_1, List.forall_mem_cons]
  exact ⟨patch_mem5_4_1_0,⟨patch_mem5_4_1_1,⟨patch_mem5_4_1_3,⟨patch_mem5_4_1_4,⟨patch_mem5_4_1_7,⟨patch_mem5_4_1_8,⟨patch_mem5_4_1_9,⟨patch_mem5_4_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq5_4_2_0 : RadiusFivePruning.stateRow5_4_2_0 = ParentOwnership.parentRow0799 := by rfl
theorem patch_mem5_4_2_0 : RadiusFivePruning.patch5_4_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0799, parentRow_mem0799, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0799_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_2_0]
  rfl
theorem row_eq5_4_2_1 : RadiusFivePruning.stateRow5_4_2_1 = ParentOwnership.parentRow0580 := by rfl
theorem patch_mem5_4_2_1 : RadiusFivePruning.patch5_4_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0580, parentRow_mem0580, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0580_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_2_1]
  rfl
theorem row_eq5_4_2_2 : RadiusFivePruning.stateRow5_4_2_2 = ParentOwnership.parentRow0666 := by rfl
theorem patch_mem5_4_2_2 : RadiusFivePruning.patch5_4_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0666, parentRow_mem0666, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0666_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_2_2]
  rfl
theorem row_eq5_4_2_3 : RadiusFivePruning.stateRow5_4_2_3 = ParentOwnership.parentRow0668 := by rfl
theorem patch_mem5_4_2_3 : RadiusFivePruning.patch5_4_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0668, parentRow_mem0668, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0668_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_2_3]
  rfl
theorem row_eq5_4_2_4 : RadiusFivePruning.stateRow5_4_2_4 = ParentOwnership.parentRow0571 := by rfl
theorem patch_mem5_4_2_4 : RadiusFivePruning.patch5_4_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0571, parentRow_mem0571, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0571_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_2_4]
  rfl
theorem row_eq5_4_2_5 : RadiusFivePruning.stateRow5_4_2_5 = ParentOwnership.parentRow0559 := by rfl
theorem patch_mem5_4_2_5 : RadiusFivePruning.patch5_4_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0559, parentRow_mem0559, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0559_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_2_5]
  rfl
theorem row_eq5_4_2_6 : RadiusFivePruning.stateRow5_4_2_6 = ParentOwnership.parentRow0667 := by rfl
theorem patch_mem5_4_2_6 : RadiusFivePruning.patch5_4_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0667, parentRow_mem0667, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0667_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_2_6]
  rfl
theorem row_eq5_4_2_7 : RadiusFivePruning.stateRow5_4_2_7 = ParentOwnership.parentRow0669 := by rfl
theorem patch_mem5_4_2_7 : RadiusFivePruning.patch5_4_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0669, parentRow_mem0669, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0669_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_2_7]
  rfl
theorem row_eq5_4_2_8 : RadiusFivePruning.stateRow5_4_2_8 = ParentOwnership.parentRow0572 := by rfl
theorem patch_mem5_4_2_8 : RadiusFivePruning.patch5_4_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0572, parentRow_mem0572, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0572_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_2_8]
  rfl
theorem row_eq5_4_2_9 : RadiusFivePruning.stateRow5_4_2_9 = ParentOwnership.parentRow0560 := by rfl
theorem patch_mem5_4_2_9 : RadiusFivePruning.patch5_4_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0560, parentRow_mem0560, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0560_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_2_9]
  rfl
theorem row_eq5_4_2_10 : RadiusFivePruning.stateRow5_4_2_10 = ParentOwnership.parentRow0664 := by rfl
theorem patch_mem5_4_2_10 : RadiusFivePruning.patch5_4_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0664, parentRow_mem0664, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0664_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_4_2_10]
  rfl
theorem chunk_mem5_4_2 : ∀ p ∈ RadiusFivePruning.final5_4_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_4_2, List.forall_mem_cons]
  exact ⟨patch_mem5_4_2_0,⟨patch_mem5_4_2_1,⟨patch_mem5_4_2_2,⟨patch_mem5_4_2_3,⟨patch_mem5_4_2_4,⟨patch_mem5_4_2_5,⟨patch_mem5_4_2_6,⟨patch_mem5_4_2_7,⟨patch_mem5_4_2_8,⟨patch_mem5_4_2_9,⟨patch_mem5_4_2_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq5_5_0_2 : RadiusFivePruning.stateRow5_5_0_2 = ParentOwnership.parentRow0269 := by rfl
theorem patch_mem5_5_0_2 : RadiusFivePruning.patch5_5_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0269, parentRow_mem0269, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0269_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_0_2]
  rfl
theorem row_eq5_5_0_3 : RadiusFivePruning.stateRow5_5_0_3 = ParentOwnership.parentRow0249 := by rfl
theorem patch_mem5_5_0_3 : RadiusFivePruning.patch5_5_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0249, parentRow_mem0249, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0249_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_0_3]
  rfl
theorem row_eq5_5_0_4 : RadiusFivePruning.stateRow5_5_0_4 = ParentOwnership.parentRow1134 := by rfl
theorem patch_mem5_5_0_4 : RadiusFivePruning.patch5_5_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1134, parentRow_mem1134, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1134_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_0_4]
  rfl
theorem row_eq5_5_0_6 : RadiusFivePruning.stateRow5_5_0_6 = ParentOwnership.parentRow0257 := by rfl
theorem patch_mem5_5_0_6 : RadiusFivePruning.patch5_5_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0257, parentRow_mem0257, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0257_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_0_6]
  rfl
theorem row_eq5_5_0_7 : RadiusFivePruning.stateRow5_5_0_7 = ParentOwnership.parentRow0258 := by rfl
theorem patch_mem5_5_0_7 : RadiusFivePruning.patch5_5_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0258, parentRow_mem0258, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0258_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_0_7]
  rfl
theorem row_eq5_5_0_9 : RadiusFivePruning.stateRow5_5_0_9 = ParentOwnership.parentRow0378 := by rfl
theorem patch_mem5_5_0_9 : RadiusFivePruning.patch5_5_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0378, parentRow_mem0378, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0378_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_0_9]
  rfl
theorem row_eq5_5_0_10 : RadiusFivePruning.stateRow5_5_0_10 = ParentOwnership.parentRow1496 := by rfl
theorem patch_mem5_5_0_10 : RadiusFivePruning.patch5_5_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1496, parentRow_mem1496, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1496_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_0_10]
  rfl
theorem row_eq5_5_0_11 : RadiusFivePruning.stateRow5_5_0_11 = ParentOwnership.parentRow1497 := by rfl
theorem patch_mem5_5_0_11 : RadiusFivePruning.patch5_5_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1497, parentRow_mem1497, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1497_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_0_11]
  rfl
theorem chunk_mem5_5_0 : ∀ p ∈ RadiusFivePruning.final5_5_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_5_0, List.forall_mem_cons]
  exact ⟨patch_mem5_5_0_2,⟨patch_mem5_5_0_3,⟨patch_mem5_5_0_4,⟨patch_mem5_5_0_6,⟨patch_mem5_5_0_7,⟨patch_mem5_5_0_9,⟨patch_mem5_5_0_10,⟨patch_mem5_5_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
