module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock7T0C6
public import SpectreFinite.RadiusFivePruningLiteralBlock7T0C7
public import SpectreFinite.RadiusFivePruningLiteralBlock7T0C8
public import SpectreFinite.RadiusFivePruningLiteralBlock7T1C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq7_0_6_0 : RadiusFivePruning.stateRow7_0_6_0 = ParentOwnership.parentRow0766 := by rfl
theorem patch_mem7_0_6_0 : RadiusFivePruning.patch7_0_6_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0766, parentRow_mem0766, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0766_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_6_0]
  rfl
theorem row_eq7_0_6_1 : RadiusFivePruning.stateRow7_0_6_1 = ParentOwnership.parentRow0767 := by rfl
theorem patch_mem7_0_6_1 : RadiusFivePruning.patch7_0_6_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0767, parentRow_mem0767, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0767_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_6_1]
  rfl
theorem row_eq7_0_6_2 : RadiusFivePruning.stateRow7_0_6_2 = ParentOwnership.parentRow0768 := by rfl
theorem patch_mem7_0_6_2 : RadiusFivePruning.patch7_0_6_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0768, parentRow_mem0768, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0768_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_6_2]
  rfl
theorem row_eq7_0_6_4 : RadiusFivePruning.stateRow7_0_6_4 = ParentOwnership.parentRow0790 := by rfl
theorem patch_mem7_0_6_4 : RadiusFivePruning.patch7_0_6_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0790, parentRow_mem0790, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0790_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_6_4]
  rfl
theorem row_eq7_0_6_6 : RadiusFivePruning.stateRow7_0_6_6 = ParentOwnership.parentRow0792 := by rfl
theorem patch_mem7_0_6_6 : RadiusFivePruning.patch7_0_6_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0792, parentRow_mem0792, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0792_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_6_6]
  rfl
theorem row_eq7_0_6_7 : RadiusFivePruning.stateRow7_0_6_7 = ParentOwnership.parentRow0793 := by rfl
theorem patch_mem7_0_6_7 : RadiusFivePruning.patch7_0_6_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0793, parentRow_mem0793, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0793_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_6_7]
  rfl
theorem row_eq7_0_6_9 : RadiusFivePruning.stateRow7_0_6_9 = ParentOwnership.parentRow0794 := by rfl
theorem patch_mem7_0_6_9 : RadiusFivePruning.patch7_0_6_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0794, parentRow_mem0794, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0794_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_6_9]
  rfl
theorem row_eq7_0_6_10 : RadiusFivePruning.stateRow7_0_6_10 = ParentOwnership.parentRow0795 := by rfl
theorem patch_mem7_0_6_10 : RadiusFivePruning.patch7_0_6_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0795, parentRow_mem0795, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0795_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_6_10]
  rfl
theorem row_eq7_0_6_11 : RadiusFivePruning.stateRow7_0_6_11 = ParentOwnership.parentRow0796 := by rfl
theorem patch_mem7_0_6_11 : RadiusFivePruning.patch7_0_6_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0796, parentRow_mem0796, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0796_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_6_11]
  rfl
theorem chunk_mem7_0_6 : ∀ p ∈ RadiusFivePruning.final7_0_6, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_0_6, List.forall_mem_cons]
  exact ⟨patch_mem7_0_6_0,⟨patch_mem7_0_6_1,⟨patch_mem7_0_6_2,⟨patch_mem7_0_6_4,⟨patch_mem7_0_6_6,⟨patch_mem7_0_6_7,⟨patch_mem7_0_6_9,⟨patch_mem7_0_6_10,⟨patch_mem7_0_6_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_0_7_0 : RadiusFivePruning.stateRow7_0_7_0 = ParentOwnership.parentRow0797 := by rfl
theorem patch_mem7_0_7_0 : RadiusFivePruning.patch7_0_7_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0797, parentRow_mem0797, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0797_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_7_0]
  rfl
theorem row_eq7_0_7_1 : RadiusFivePruning.stateRow7_0_7_1 = ParentOwnership.parentRow2003 := by rfl
theorem patch_mem7_0_7_1 : RadiusFivePruning.patch7_0_7_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2003, parentRow_mem2003, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2003_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_7_1]
  rfl
theorem row_eq7_0_7_2 : RadiusFivePruning.stateRow7_0_7_2 = ParentOwnership.parentRow2004 := by rfl
theorem patch_mem7_0_7_2 : RadiusFivePruning.patch7_0_7_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2004, parentRow_mem2004, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2004_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_7_2]
  rfl
theorem row_eq7_0_7_3 : RadiusFivePruning.stateRow7_0_7_3 = ParentOwnership.parentRow2006 := by rfl
theorem patch_mem7_0_7_3 : RadiusFivePruning.patch7_0_7_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2006, parentRow_mem2006, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2006_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_7_3]
  rfl
theorem row_eq7_0_7_4 : RadiusFivePruning.stateRow7_0_7_4 = ParentOwnership.parentRow2007 := by rfl
theorem patch_mem7_0_7_4 : RadiusFivePruning.patch7_0_7_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2007, parentRow_mem2007, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2007_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_7_4]
  rfl
theorem row_eq7_0_7_5 : RadiusFivePruning.stateRow7_0_7_5 = ParentOwnership.parentRow0573 := by rfl
theorem patch_mem7_0_7_5 : RadiusFivePruning.patch7_0_7_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0573, parentRow_mem0573, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0573_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_7_5]
  rfl
theorem row_eq7_0_7_6 : RadiusFivePruning.stateRow7_0_7_6 = ParentOwnership.parentRow0574 := by rfl
theorem patch_mem7_0_7_6 : RadiusFivePruning.patch7_0_7_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0574, parentRow_mem0574, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0574_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_7_6]
  rfl
theorem row_eq7_0_7_11 : RadiusFivePruning.stateRow7_0_7_11 = ParentOwnership.parentRow0575 := by rfl
theorem patch_mem7_0_7_11 : RadiusFivePruning.patch7_0_7_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0575, parentRow_mem0575, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0575_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_7_11]
  rfl
theorem chunk_mem7_0_7 : ∀ p ∈ RadiusFivePruning.final7_0_7, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_0_7, List.forall_mem_cons]
  exact ⟨patch_mem7_0_7_0,⟨patch_mem7_0_7_1,⟨patch_mem7_0_7_2,⟨patch_mem7_0_7_3,⟨patch_mem7_0_7_4,⟨patch_mem7_0_7_5,⟨patch_mem7_0_7_6,⟨patch_mem7_0_7_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_0_8_0 : RadiusFivePruning.stateRow7_0_8_0 = ParentOwnership.parentRow0576 := by rfl
theorem patch_mem7_0_8_0 : RadiusFivePruning.patch7_0_8_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0576, parentRow_mem0576, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0576_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_8_0]
  rfl
theorem row_eq7_0_8_1 : RadiusFivePruning.stateRow7_0_8_1 = ParentOwnership.parentRow0577 := by rfl
theorem patch_mem7_0_8_1 : RadiusFivePruning.patch7_0_8_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0577, parentRow_mem0577, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0577_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_8_1]
  rfl
theorem row_eq7_0_8_2 : RadiusFivePruning.stateRow7_0_8_2 = ParentOwnership.parentRow0578 := by rfl
theorem patch_mem7_0_8_2 : RadiusFivePruning.patch7_0_8_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0578, parentRow_mem0578, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0578_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_8_2]
  rfl
theorem row_eq7_0_8_3 : RadiusFivePruning.stateRow7_0_8_3 = ParentOwnership.parentRow0579 := by rfl
theorem patch_mem7_0_8_3 : RadiusFivePruning.patch7_0_8_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0579, parentRow_mem0579, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0579_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_8_3]
  rfl
theorem row_eq7_0_8_5 : RadiusFivePruning.stateRow7_0_8_5 = ParentOwnership.parentRow1629 := by rfl
theorem patch_mem7_0_8_5 : RadiusFivePruning.patch7_0_8_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1629, parentRow_mem1629, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1629_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_8_5]
  rfl
theorem row_eq7_0_8_7 : RadiusFivePruning.stateRow7_0_8_7 = ParentOwnership.parentRow1630 := by rfl
theorem patch_mem7_0_8_7 : RadiusFivePruning.patch7_0_8_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1630, parentRow_mem1630, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1630_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_8_7]
  rfl
theorem row_eq7_0_8_8 : RadiusFivePruning.stateRow7_0_8_8 = ParentOwnership.parentRow1631 := by rfl
theorem patch_mem7_0_8_8 : RadiusFivePruning.patch7_0_8_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1631, parentRow_mem1631, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1631_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_8_8]
  rfl
theorem row_eq7_0_8_9 : RadiusFivePruning.stateRow7_0_8_9 = ParentOwnership.parentRow1634 := by rfl
theorem patch_mem7_0_8_9 : RadiusFivePruning.patch7_0_8_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1634, parentRow_mem1634, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1634_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_0_8_9]
  rfl
theorem chunk_mem7_0_8 : ∀ p ∈ RadiusFivePruning.final7_0_8, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_0_8, List.forall_mem_cons]
  exact ⟨patch_mem7_0_8_0,⟨patch_mem7_0_8_1,⟨patch_mem7_0_8_2,⟨patch_mem7_0_8_3,⟨patch_mem7_0_8_5,⟨patch_mem7_0_8_7,⟨patch_mem7_0_8_8,⟨patch_mem7_0_8_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_1_0_1 : RadiusFivePruning.stateRow7_1_0_1 = ParentOwnership.parentRow0933 := by rfl
theorem patch_mem7_1_0_1 : RadiusFivePruning.patch7_1_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0933, parentRow_mem0933, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0933_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_0_1]
  rfl
theorem row_eq7_1_0_2 : RadiusFivePruning.stateRow7_1_0_2 = ParentOwnership.parentRow0951 := by rfl
theorem patch_mem7_1_0_2 : RadiusFivePruning.patch7_1_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0951, parentRow_mem0951, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0951_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_0_2]
  rfl
theorem row_eq7_1_0_3 : RadiusFivePruning.stateRow7_1_0_3 = ParentOwnership.parentRow0952 := by rfl
theorem patch_mem7_1_0_3 : RadiusFivePruning.patch7_1_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0952, parentRow_mem0952, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0952_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_0_3]
  rfl
theorem row_eq7_1_0_4 : RadiusFivePruning.stateRow7_1_0_4 = ParentOwnership.parentRow0944 := by rfl
theorem patch_mem7_1_0_4 : RadiusFivePruning.patch7_1_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0944, parentRow_mem0944, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0944_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_0_4]
  rfl
theorem row_eq7_1_0_5 : RadiusFivePruning.stateRow7_1_0_5 = ParentOwnership.parentRow0945 := by rfl
theorem patch_mem7_1_0_5 : RadiusFivePruning.patch7_1_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0945, parentRow_mem0945, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0945_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_0_5]
  rfl
theorem row_eq7_1_0_6 : RadiusFivePruning.stateRow7_1_0_6 = ParentOwnership.parentRow0953 := by rfl
theorem patch_mem7_1_0_6 : RadiusFivePruning.patch7_1_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0953, parentRow_mem0953, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0953_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_0_6]
  rfl
theorem row_eq7_1_0_7 : RadiusFivePruning.stateRow7_1_0_7 = ParentOwnership.parentRow0954 := by rfl
theorem patch_mem7_1_0_7 : RadiusFivePruning.patch7_1_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0954, parentRow_mem0954, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0954_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_0_7]
  rfl
theorem row_eq7_1_0_8 : RadiusFivePruning.stateRow7_1_0_8 = ParentOwnership.parentRow0915 := by rfl
theorem patch_mem7_1_0_8 : RadiusFivePruning.patch7_1_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0915, parentRow_mem0915, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0915_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_0_8]
  rfl
theorem row_eq7_1_0_11 : RadiusFivePruning.stateRow7_1_0_11 = ParentOwnership.parentRow0911 := by rfl
theorem patch_mem7_1_0_11 : RadiusFivePruning.patch7_1_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0911, parentRow_mem0911, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0911_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_1_0_11]
  rfl
theorem chunk_mem7_1_0 : ∀ p ∈ RadiusFivePruning.final7_1_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_1_0, List.forall_mem_cons]
  exact ⟨patch_mem7_1_0_1,⟨patch_mem7_1_0_2,⟨patch_mem7_1_0_3,⟨patch_mem7_1_0_4,⟨patch_mem7_1_0_5,⟨patch_mem7_1_0_6,⟨patch_mem7_1_0_7,⟨patch_mem7_1_0_8,⟨patch_mem7_1_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
