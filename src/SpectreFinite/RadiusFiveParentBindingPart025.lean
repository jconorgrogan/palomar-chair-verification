module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock5T1C1
public import SpectreFinite.RadiusFivePruningLiteralBlock5T1C2
public import SpectreFinite.RadiusFivePruningLiteralBlock5T2C0
public import SpectreFinite.RadiusFivePruningLiteralBlock5T2C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq5_1_1_0 : RadiusFivePruning.stateRow5_1_1_0 = ParentOwnership.parentRow1420 := by rfl
theorem patch_mem5_1_1_0 : RadiusFivePruning.patch5_1_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1420, parentRow_mem1420, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1420_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_1_0]
  rfl
theorem row_eq5_1_1_1 : RadiusFivePruning.stateRow5_1_1_1 = ParentOwnership.parentRow0744 := by rfl
theorem patch_mem5_1_1_1 : RadiusFivePruning.patch5_1_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0744, parentRow_mem0744, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0744_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_1_1]
  rfl
theorem row_eq5_1_1_3 : RadiusFivePruning.stateRow5_1_1_3 = ParentOwnership.parentRow0748 := by rfl
theorem patch_mem5_1_1_3 : RadiusFivePruning.patch5_1_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0748, parentRow_mem0748, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0748_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_1_3]
  rfl
theorem row_eq5_1_1_4 : RadiusFivePruning.stateRow5_1_1_4 = ParentOwnership.parentRow0747 := by rfl
theorem patch_mem5_1_1_4 : RadiusFivePruning.patch5_1_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0747, parentRow_mem0747, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0747_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_1_4]
  rfl
theorem row_eq5_1_1_7 : RadiusFivePruning.stateRow5_1_1_7 = ParentOwnership.parentRow0743 := by rfl
theorem patch_mem5_1_1_7 : RadiusFivePruning.patch5_1_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0743, parentRow_mem0743, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0743_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_1_7]
  rfl
theorem row_eq5_1_1_8 : RadiusFivePruning.stateRow5_1_1_8 = ParentOwnership.parentRow0745 := by rfl
theorem patch_mem5_1_1_8 : RadiusFivePruning.patch5_1_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0745, parentRow_mem0745, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0745_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_1_8]
  rfl
theorem row_eq5_1_1_9 : RadiusFivePruning.stateRow5_1_1_9 = ParentOwnership.parentRow0746 := by rfl
theorem patch_mem5_1_1_9 : RadiusFivePruning.patch5_1_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0746, parentRow_mem0746, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0746_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_1_9]
  rfl
theorem row_eq5_1_1_11 : RadiusFivePruning.stateRow5_1_1_11 = ParentOwnership.parentRow0751 := by rfl
theorem patch_mem5_1_1_11 : RadiusFivePruning.patch5_1_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0751, parentRow_mem0751, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0751_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_1_11]
  rfl
theorem chunk_mem5_1_1 : ∀ p ∈ RadiusFivePruning.final5_1_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_1_1, List.forall_mem_cons]
  exact ⟨patch_mem5_1_1_0,⟨patch_mem5_1_1_1,⟨patch_mem5_1_1_3,⟨patch_mem5_1_1_4,⟨patch_mem5_1_1_7,⟨patch_mem5_1_1_8,⟨patch_mem5_1_1_9,⟨patch_mem5_1_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq5_1_2_0 : RadiusFivePruning.stateRow5_1_2_0 = ParentOwnership.parentRow0750 := by rfl
theorem patch_mem5_1_2_0 : RadiusFivePruning.patch5_1_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0750, parentRow_mem0750, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0750_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_2_0]
  rfl
theorem row_eq5_1_2_1 : RadiusFivePruning.stateRow5_1_2_1 = ParentOwnership.parentRow0749 := by rfl
theorem patch_mem5_1_2_1 : RadiusFivePruning.patch5_1_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0749, parentRow_mem0749, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0749_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_2_1]
  rfl
theorem row_eq5_1_2_2 : RadiusFivePruning.stateRow5_1_2_2 = ParentOwnership.parentRow0740 := by rfl
theorem patch_mem5_1_2_2 : RadiusFivePruning.patch5_1_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0740, parentRow_mem0740, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0740_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_2_2]
  rfl
theorem row_eq5_1_2_3 : RadiusFivePruning.stateRow5_1_2_3 = ParentOwnership.parentRow0742 := by rfl
theorem patch_mem5_1_2_3 : RadiusFivePruning.patch5_1_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0742, parentRow_mem0742, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0742_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_2_3]
  rfl
theorem row_eq5_1_2_4 : RadiusFivePruning.stateRow5_1_2_4 = ParentOwnership.parentRow0739 := by rfl
theorem patch_mem5_1_2_4 : RadiusFivePruning.patch5_1_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0739, parentRow_mem0739, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0739_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_2_4]
  rfl
theorem row_eq5_1_2_5 : RadiusFivePruning.stateRow5_1_2_5 = ParentOwnership.parentRow0741 := by rfl
theorem patch_mem5_1_2_5 : RadiusFivePruning.patch5_1_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0741, parentRow_mem0741, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0741_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_2_5]
  rfl
theorem row_eq5_1_2_6 : RadiusFivePruning.stateRow5_1_2_6 = ParentOwnership.parentRow0727 := by rfl
theorem patch_mem5_1_2_6 : RadiusFivePruning.patch5_1_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0727, parentRow_mem0727, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0727_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_2_6]
  rfl
theorem row_eq5_1_2_7 : RadiusFivePruning.stateRow5_1_2_7 = ParentOwnership.parentRow0729 := by rfl
theorem patch_mem5_1_2_7 : RadiusFivePruning.patch5_1_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0729, parentRow_mem0729, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0729_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_2_7]
  rfl
theorem row_eq5_1_2_8 : RadiusFivePruning.stateRow5_1_2_8 = ParentOwnership.parentRow0726 := by rfl
theorem patch_mem5_1_2_8 : RadiusFivePruning.patch5_1_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0726, parentRow_mem0726, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0726_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_2_8]
  rfl
theorem row_eq5_1_2_9 : RadiusFivePruning.stateRow5_1_2_9 = ParentOwnership.parentRow0728 := by rfl
theorem patch_mem5_1_2_9 : RadiusFivePruning.patch5_1_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0728, parentRow_mem0728, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0728_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_2_9]
  rfl
theorem row_eq5_1_2_10 : RadiusFivePruning.stateRow5_1_2_10 = ParentOwnership.parentRow0738 := by rfl
theorem patch_mem5_1_2_10 : RadiusFivePruning.patch5_1_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0738, parentRow_mem0738, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0738_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_1_2_10]
  rfl
theorem chunk_mem5_1_2 : ∀ p ∈ RadiusFivePruning.final5_1_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_1_2, List.forall_mem_cons]
  exact ⟨patch_mem5_1_2_0,⟨patch_mem5_1_2_1,⟨patch_mem5_1_2_2,⟨patch_mem5_1_2_3,⟨patch_mem5_1_2_4,⟨patch_mem5_1_2_5,⟨patch_mem5_1_2_6,⟨patch_mem5_1_2_7,⟨patch_mem5_1_2_8,⟨patch_mem5_1_2_9,⟨patch_mem5_1_2_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq5_2_0_2 : RadiusFivePruning.stateRow5_2_0_2 = ParentOwnership.parentRow0377 := by rfl
theorem patch_mem5_2_0_2 : RadiusFivePruning.patch5_2_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0377, parentRow_mem0377, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0377_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_0_2]
  rfl
theorem row_eq5_2_0_3 : RadiusFivePruning.stateRow5_2_0_3 = ParentOwnership.parentRow0376 := by rfl
theorem patch_mem5_2_0_3 : RadiusFivePruning.patch5_2_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0376, parentRow_mem0376, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0376_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_0_3]
  rfl
theorem row_eq5_2_0_4 : RadiusFivePruning.stateRow5_2_0_4 = ParentOwnership.parentRow1494 := by rfl
theorem patch_mem5_2_0_4 : RadiusFivePruning.patch5_2_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1494, parentRow_mem1494, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1494_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_0_4]
  rfl
theorem row_eq5_2_0_6 : RadiusFivePruning.stateRow5_2_0_6 = ParentOwnership.parentRow1495 := by rfl
theorem patch_mem5_2_0_6 : RadiusFivePruning.patch5_2_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1495, parentRow_mem1495, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1495_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_0_6]
  rfl
theorem row_eq5_2_0_7 : RadiusFivePruning.stateRow5_2_0_7 = ParentOwnership.parentRow1493 := by rfl
theorem patch_mem5_2_0_7 : RadiusFivePruning.patch5_2_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1493, parentRow_mem1493, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1493_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_0_7]
  rfl
theorem row_eq5_2_0_9 : RadiusFivePruning.stateRow5_2_0_9 = ParentOwnership.parentRow1145 := by rfl
theorem patch_mem5_2_0_9 : RadiusFivePruning.patch5_2_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1145, parentRow_mem1145, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1145_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_0_9]
  rfl
theorem row_eq5_2_0_10 : RadiusFivePruning.stateRow5_2_0_10 = ParentOwnership.parentRow1153 := by rfl
theorem patch_mem5_2_0_10 : RadiusFivePruning.patch5_2_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1153, parentRow_mem1153, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1153_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_0_10]
  rfl
theorem row_eq5_2_0_11 : RadiusFivePruning.stateRow5_2_0_11 = ParentOwnership.parentRow1146 := by rfl
theorem patch_mem5_2_0_11 : RadiusFivePruning.patch5_2_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1146, parentRow_mem1146, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1146_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_0_11]
  rfl
theorem chunk_mem5_2_0 : ∀ p ∈ RadiusFivePruning.final5_2_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_2_0, List.forall_mem_cons]
  exact ⟨patch_mem5_2_0_2,⟨patch_mem5_2_0_3,⟨patch_mem5_2_0_4,⟨patch_mem5_2_0_6,⟨patch_mem5_2_0_7,⟨patch_mem5_2_0_9,⟨patch_mem5_2_0_10,⟨patch_mem5_2_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq5_2_1_0 : RadiusFivePruning.stateRow5_2_1_0 = ParentOwnership.parentRow0270 := by rfl
theorem patch_mem5_2_1_0 : RadiusFivePruning.patch5_2_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0270, parentRow_mem0270, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0270_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_1_0]
  rfl
theorem row_eq5_2_1_1 : RadiusFivePruning.stateRow5_2_1_1 = ParentOwnership.parentRow1131 := by rfl
theorem patch_mem5_2_1_1 : RadiusFivePruning.patch5_2_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1131, parentRow_mem1131, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1131_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_1_1]
  rfl
theorem row_eq5_2_1_3 : RadiusFivePruning.stateRow5_2_1_3 = ParentOwnership.parentRow1147 := by rfl
theorem patch_mem5_2_1_3 : RadiusFivePruning.patch5_2_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1147, parentRow_mem1147, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1147_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_1_3]
  rfl
theorem row_eq5_2_1_4 : RadiusFivePruning.stateRow5_2_1_4 = ParentOwnership.parentRow1143 := by rfl
theorem patch_mem5_2_1_4 : RadiusFivePruning.patch5_2_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1143, parentRow_mem1143, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1143_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_1_4]
  rfl
theorem row_eq5_2_1_7 : RadiusFivePruning.stateRow5_2_1_7 = ParentOwnership.parentRow1128 := by rfl
theorem patch_mem5_2_1_7 : RadiusFivePruning.patch5_2_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1128, parentRow_mem1128, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1128_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_1_7]
  rfl
theorem row_eq5_2_1_8 : RadiusFivePruning.stateRow5_2_1_8 = ParentOwnership.parentRow1129 := by rfl
theorem patch_mem5_2_1_8 : RadiusFivePruning.patch5_2_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1129, parentRow_mem1129, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1129_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_1_8]
  rfl
theorem row_eq5_2_1_9 : RadiusFivePruning.stateRow5_2_1_9 = ParentOwnership.parentRow1130 := by rfl
theorem patch_mem5_2_1_9 : RadiusFivePruning.patch5_2_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1130, parentRow_mem1130, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1130_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_1_9]
  rfl
theorem row_eq5_2_1_11 : RadiusFivePruning.stateRow5_2_1_11 = ParentOwnership.parentRow0244 := by rfl
theorem patch_mem5_2_1_11 : RadiusFivePruning.patch5_2_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0244, parentRow_mem0244, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0244_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_2_1_11]
  rfl
theorem chunk_mem5_2_1 : ∀ p ∈ RadiusFivePruning.final5_2_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_2_1, List.forall_mem_cons]
  exact ⟨patch_mem5_2_1_0,⟨patch_mem5_2_1_1,⟨patch_mem5_2_1_3,⟨patch_mem5_2_1_4,⟨patch_mem5_2_1_7,⟨patch_mem5_2_1_8,⟨patch_mem5_2_1_9,⟨patch_mem5_2_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
