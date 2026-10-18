module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock7T1C1
public import SpectreFinite.RadiusFivePruningLiteralBlock7T1C2
public import SpectreFinite.RadiusFivePruningLiteralBlock7T1C3
public import SpectreFinite.RadiusFivePruningLiteralBlock7T1C4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq7_1_1_0 : RadiusFivePruning.stateRow7_1_1_0 = ParentOwnership.parentRow0912 := by rfl
theorem patch_mem7_1_1_0 : RadiusFivePruning.patch7_1_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0912, parentRow_mem0912, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0912_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_1_0]
  rfl
theorem row_eq7_1_1_2 : RadiusFivePruning.stateRow7_1_1_2 = ParentOwnership.parentRow0913 := by rfl
theorem patch_mem7_1_1_2 : RadiusFivePruning.patch7_1_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0913, parentRow_mem0913, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0913_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_1_2]
  rfl
theorem row_eq7_1_1_3 : RadiusFivePruning.stateRow7_1_1_3 = ParentOwnership.parentRow0916 := by rfl
theorem patch_mem7_1_1_3 : RadiusFivePruning.patch7_1_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0916, parentRow_mem0916, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0916_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_1_3]
  rfl
theorem row_eq7_1_1_4 : RadiusFivePruning.stateRow7_1_1_4 = ParentOwnership.parentRow0914 := by rfl
theorem patch_mem7_1_1_4 : RadiusFivePruning.patch7_1_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0914, parentRow_mem0914, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0914_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_1_4]
  rfl
theorem row_eq7_1_1_5 : RadiusFivePruning.stateRow7_1_1_5 = ParentOwnership.parentRow0917 := by rfl
theorem patch_mem7_1_1_5 : RadiusFivePruning.patch7_1_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0917, parentRow_mem0917, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0917_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_1_5]
  rfl
theorem row_eq7_1_1_6 : RadiusFivePruning.stateRow7_1_1_6 = ParentOwnership.parentRow0601 := by rfl
theorem patch_mem7_1_1_6 : RadiusFivePruning.patch7_1_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0601, parentRow_mem0601, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0601_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_1_6]
  rfl
theorem row_eq7_1_1_9 : RadiusFivePruning.stateRow7_1_1_9 = ParentOwnership.parentRow0603 := by rfl
theorem patch_mem7_1_1_9 : RadiusFivePruning.patch7_1_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0603, parentRow_mem0603, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0603_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_1_9]
  rfl
theorem row_eq7_1_1_10 : RadiusFivePruning.stateRow7_1_1_10 = ParentOwnership.parentRow0605 := by rfl
theorem patch_mem7_1_1_10 : RadiusFivePruning.patch7_1_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0605, parentRow_mem0605, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0605_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_1_10]
  rfl
theorem row_eq7_1_1_11 : RadiusFivePruning.stateRow7_1_1_11 = ParentOwnership.parentRow0599 := by rfl
theorem patch_mem7_1_1_11 : RadiusFivePruning.patch7_1_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0599, parentRow_mem0599, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0599_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_1_11]
  rfl
theorem chunk_mem7_1_1 : ∀ p ∈ RadiusFivePruning.final7_1_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_1_1, List.forall_mem_cons]
  exact ⟨patch_mem7_1_1_0,⟨patch_mem7_1_1_2,⟨patch_mem7_1_1_3,⟨patch_mem7_1_1_4,⟨patch_mem7_1_1_5,⟨patch_mem7_1_1_6,⟨patch_mem7_1_1_9,⟨patch_mem7_1_1_10,⟨patch_mem7_1_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_1_2_0 : RadiusFivePruning.stateRow7_1_2_0 = ParentOwnership.parentRow0600 := by rfl
theorem patch_mem7_1_2_0 : RadiusFivePruning.patch7_1_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0600, parentRow_mem0600, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0600_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_2_0]
  rfl
theorem row_eq7_1_2_1 : RadiusFivePruning.stateRow7_1_2_1 = ParentOwnership.parentRow0602 := by rfl
theorem patch_mem7_1_2_1 : RadiusFivePruning.patch7_1_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0602, parentRow_mem0602, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0602_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_2_1]
  rfl
theorem row_eq7_1_2_2 : RadiusFivePruning.stateRow7_1_2_2 = ParentOwnership.parentRow0604 := by rfl
theorem patch_mem7_1_2_2 : RadiusFivePruning.patch7_1_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0604, parentRow_mem0604, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0604_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_2_2]
  rfl
theorem row_eq7_1_2_3 : RadiusFivePruning.stateRow7_1_2_3 = ParentOwnership.parentRow1569 := by rfl
theorem patch_mem7_1_2_3 : RadiusFivePruning.patch7_1_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1569, parentRow_mem1569, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1569_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_2_3]
  rfl
theorem row_eq7_1_2_4 : RadiusFivePruning.stateRow7_1_2_4 = ParentOwnership.parentRow1562 := by rfl
theorem patch_mem7_1_2_4 : RadiusFivePruning.patch7_1_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1562, parentRow_mem1562, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1562_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_2_4]
  rfl
theorem row_eq7_1_2_5 : RadiusFivePruning.stateRow7_1_2_5 = ParentOwnership.parentRow1565 := by rfl
theorem patch_mem7_1_2_5 : RadiusFivePruning.patch7_1_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1565, parentRow_mem1565, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1565_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_2_5]
  rfl
theorem row_eq7_1_2_6 : RadiusFivePruning.stateRow7_1_2_6 = ParentOwnership.parentRow1568 := by rfl
theorem patch_mem7_1_2_6 : RadiusFivePruning.patch7_1_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1568, parentRow_mem1568, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1568_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_2_6]
  rfl
theorem row_eq7_1_2_8 : RadiusFivePruning.stateRow7_1_2_8 = ParentOwnership.parentRow0948 := by rfl
theorem patch_mem7_1_2_8 : RadiusFivePruning.patch7_1_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0948, parentRow_mem0948, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0948_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_2_8]
  rfl
theorem row_eq7_1_2_10 : RadiusFivePruning.stateRow7_1_2_10 = ParentOwnership.parentRow0946 := by rfl
theorem patch_mem7_1_2_10 : RadiusFivePruning.patch7_1_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0946, parentRow_mem0946, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0946_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_2_10]
  rfl
theorem row_eq7_1_2_11 : RadiusFivePruning.stateRow7_1_2_11 = ParentOwnership.parentRow0947 := by rfl
theorem patch_mem7_1_2_11 : RadiusFivePruning.patch7_1_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0947, parentRow_mem0947, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0947_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_2_11]
  rfl
theorem chunk_mem7_1_2 : ∀ p ∈ RadiusFivePruning.final7_1_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_1_2, List.forall_mem_cons]
  exact ⟨patch_mem7_1_2_0,⟨patch_mem7_1_2_1,⟨patch_mem7_1_2_2,⟨patch_mem7_1_2_3,⟨patch_mem7_1_2_4,⟨patch_mem7_1_2_5,⟨patch_mem7_1_2_6,⟨patch_mem7_1_2_8,⟨patch_mem7_1_2_10,⟨patch_mem7_1_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_1_3_0 : RadiusFivePruning.stateRow7_1_3_0 = ParentOwnership.parentRow0935 := by rfl
theorem patch_mem7_1_3_0 : RadiusFivePruning.patch7_1_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0935, parentRow_mem0935, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0935_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_3_0]
  rfl
theorem row_eq7_1_3_1 : RadiusFivePruning.stateRow7_1_3_1 = ParentOwnership.parentRow0936 := by rfl
theorem patch_mem7_1_3_1 : RadiusFivePruning.patch7_1_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0936, parentRow_mem0936, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0936_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_3_1]
  rfl
theorem row_eq7_1_3_2 : RadiusFivePruning.stateRow7_1_3_2 = ParentOwnership.parentRow0949 := by rfl
theorem patch_mem7_1_3_2 : RadiusFivePruning.patch7_1_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0949, parentRow_mem0949, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0949_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_3_2]
  rfl
theorem row_eq7_1_3_3 : RadiusFivePruning.stateRow7_1_3_3 = ParentOwnership.parentRow0950 := by rfl
theorem patch_mem7_1_3_3 : RadiusFivePruning.patch7_1_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0950, parentRow_mem0950, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0950_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_3_3]
  rfl
theorem row_eq7_1_3_5 : RadiusFivePruning.stateRow7_1_3_5 = ParentOwnership.parentRow1777 := by rfl
theorem patch_mem7_1_3_5 : RadiusFivePruning.patch7_1_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1777, parentRow_mem1777, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1777_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_3_5]
  rfl
theorem row_eq7_1_3_6 : RadiusFivePruning.stateRow7_1_3_6 = ParentOwnership.parentRow1780 := by rfl
theorem patch_mem7_1_3_6 : RadiusFivePruning.patch7_1_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1780, parentRow_mem1780, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1780_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_3_6]
  rfl
theorem row_eq7_1_3_7 : RadiusFivePruning.stateRow7_1_3_7 = ParentOwnership.parentRow1762 := by rfl
theorem patch_mem7_1_3_7 : RadiusFivePruning.patch7_1_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1762, parentRow_mem1762, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1762_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_3_7]
  rfl
theorem row_eq7_1_3_8 : RadiusFivePruning.stateRow7_1_3_8 = ParentOwnership.parentRow1775 := by rfl
theorem patch_mem7_1_3_8 : RadiusFivePruning.patch7_1_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1775, parentRow_mem1775, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1775_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_3_8]
  rfl
theorem row_eq7_1_3_9 : RadiusFivePruning.stateRow7_1_3_9 = ParentOwnership.parentRow1776 := by rfl
theorem patch_mem7_1_3_9 : RadiusFivePruning.patch7_1_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1776, parentRow_mem1776, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1776_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_3_9]
  rfl
theorem row_eq7_1_3_10 : RadiusFivePruning.stateRow7_1_3_10 = ParentOwnership.parentRow1779 := by rfl
theorem patch_mem7_1_3_10 : RadiusFivePruning.patch7_1_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1779, parentRow_mem1779, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1779_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_3_10]
  rfl
theorem row_eq7_1_3_11 : RadiusFivePruning.stateRow7_1_3_11 = ParentOwnership.parentRow1778 := by rfl
theorem patch_mem7_1_3_11 : RadiusFivePruning.patch7_1_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1778, parentRow_mem1778, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1778_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_3_11]
  rfl
theorem chunk_mem7_1_3 : ∀ p ∈ RadiusFivePruning.final7_1_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_1_3, List.forall_mem_cons]
  exact ⟨patch_mem7_1_3_0,⟨patch_mem7_1_3_1,⟨patch_mem7_1_3_2,⟨patch_mem7_1_3_3,⟨patch_mem7_1_3_5,⟨patch_mem7_1_3_6,⟨patch_mem7_1_3_7,⟨patch_mem7_1_3_8,⟨patch_mem7_1_3_9,⟨patch_mem7_1_3_10,⟨patch_mem7_1_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_1_4_1 : RadiusFivePruning.stateRow7_1_4_1 = ParentOwnership.parentRow0849 := by rfl
theorem patch_mem7_1_4_1 : RadiusFivePruning.patch7_1_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0849, parentRow_mem0849, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0849_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_4_1]
  rfl
theorem row_eq7_1_4_2 : RadiusFivePruning.stateRow7_1_4_2 = ParentOwnership.parentRow0852 := by rfl
theorem patch_mem7_1_4_2 : RadiusFivePruning.patch7_1_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0852, parentRow_mem0852, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0852_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_4_2]
  rfl
theorem row_eq7_1_4_3 : RadiusFivePruning.stateRow7_1_4_3 = ParentOwnership.parentRow0839 := by rfl
theorem patch_mem7_1_4_3 : RadiusFivePruning.patch7_1_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0839, parentRow_mem0839, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0839_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_4_3]
  rfl
theorem row_eq7_1_4_4 : RadiusFivePruning.stateRow7_1_4_4 = ParentOwnership.parentRow0850 := by rfl
theorem patch_mem7_1_4_4 : RadiusFivePruning.patch7_1_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0850, parentRow_mem0850, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0850_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_4_4]
  rfl
theorem row_eq7_1_4_5 : RadiusFivePruning.stateRow7_1_4_5 = ParentOwnership.parentRow0851 := by rfl
theorem patch_mem7_1_4_5 : RadiusFivePruning.patch7_1_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0851, parentRow_mem0851, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0851_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_4_5]
  rfl
theorem row_eq7_1_4_8 : RadiusFivePruning.stateRow7_1_4_8 = ParentOwnership.parentRow1761 := by rfl
theorem patch_mem7_1_4_8 : RadiusFivePruning.patch7_1_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1761, parentRow_mem1761, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1761_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_4_8]
  rfl
theorem row_eq7_1_4_10 : RadiusFivePruning.stateRow7_1_4_10 = ParentOwnership.parentRow1795 := by rfl
theorem patch_mem7_1_4_10 : RadiusFivePruning.patch7_1_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1795, parentRow_mem1795, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1795_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_4_10]
  rfl
theorem chunk_mem7_1_4 : ∀ p ∈ RadiusFivePruning.final7_1_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_1_4, List.forall_mem_cons]
  exact ⟨patch_mem7_1_4_1,⟨patch_mem7_1_4_2,⟨patch_mem7_1_4_3,⟨patch_mem7_1_4_4,⟨patch_mem7_1_4_5,⟨patch_mem7_1_4_8,⟨patch_mem7_1_4_10,by simp⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
