module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock4T2C0
public import SpectreFinite.RadiusFivePruningLiteralBlock4T2C1
public import SpectreFinite.RadiusFivePruningLiteralBlock4T2C2
public import SpectreFinite.RadiusFivePruningLiteralBlock4T2C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq4_2_0_1 : RadiusFivePruning.stateRow4_2_0_1 = ParentOwnership.parentRow1523 := by rfl
theorem patch_mem4_2_0_1 : RadiusFivePruning.patch4_2_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1523, parentRow_mem1523, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1523_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_0_1]
  rfl
theorem row_eq4_2_0_3 : RadiusFivePruning.stateRow4_2_0_3 = ParentOwnership.parentRow1520 := by rfl
theorem patch_mem4_2_0_3 : RadiusFivePruning.patch4_2_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1520, parentRow_mem1520, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1520_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_0_3]
  rfl
theorem row_eq4_2_0_4 : RadiusFivePruning.stateRow4_2_0_4 = ParentOwnership.parentRow0863 := by rfl
theorem patch_mem4_2_0_4 : RadiusFivePruning.patch4_2_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0863, parentRow_mem0863, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0863_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_0_4]
  rfl
theorem row_eq4_2_0_6 : RadiusFivePruning.stateRow4_2_0_6 = ParentOwnership.parentRow0786 := by rfl
theorem patch_mem4_2_0_6 : RadiusFivePruning.patch4_2_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0786, parentRow_mem0786, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0786_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_0_6]
  rfl
theorem row_eq4_2_0_7 : RadiusFivePruning.stateRow4_2_0_7 = ParentOwnership.parentRow0787 := by rfl
theorem patch_mem4_2_0_7 : RadiusFivePruning.patch4_2_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0787, parentRow_mem0787, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0787_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_0_7]
  rfl
theorem row_eq4_2_0_9 : RadiusFivePruning.stateRow4_2_0_9 = ParentOwnership.parentRow2036 := by rfl
theorem patch_mem4_2_0_9 : RadiusFivePruning.patch4_2_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2036, parentRow_mem2036, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2036_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_0_9]
  rfl
theorem row_eq4_2_0_10 : RadiusFivePruning.stateRow4_2_0_10 = ParentOwnership.parentRow2037 := by rfl
theorem patch_mem4_2_0_10 : RadiusFivePruning.patch4_2_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2037, parentRow_mem2037, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2037_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_0_10]
  rfl
theorem row_eq4_2_0_11 : RadiusFivePruning.stateRow4_2_0_11 = ParentOwnership.parentRow2040 := by rfl
theorem patch_mem4_2_0_11 : RadiusFivePruning.patch4_2_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2040, parentRow_mem2040, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2040_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_0_11]
  rfl
theorem chunk_mem4_2_0 : ∀ p ∈ RadiusFivePruning.final4_2_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_2_0, List.forall_mem_cons]
  exact ⟨patch_mem4_2_0_1,⟨patch_mem4_2_0_3,⟨patch_mem4_2_0_4,⟨patch_mem4_2_0_6,⟨patch_mem4_2_0_7,⟨patch_mem4_2_0_9,⟨patch_mem4_2_0_10,⟨patch_mem4_2_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_2_1_0 : RadiusFivePruning.stateRow4_2_1_0 = ParentOwnership.parentRow0961 := by rfl
theorem patch_mem4_2_1_0 : RadiusFivePruning.patch4_2_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0961, parentRow_mem0961, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0961_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_1_0]
  rfl
theorem row_eq4_2_1_1 : RadiusFivePruning.stateRow4_2_1_1 = ParentOwnership.parentRow0963 := by rfl
theorem patch_mem4_2_1_1 : RadiusFivePruning.patch4_2_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0963, parentRow_mem0963, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0963_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_1_1]
  rfl
theorem row_eq4_2_1_3 : RadiusFivePruning.stateRow4_2_1_3 = ParentOwnership.parentRow0965 := by rfl
theorem patch_mem4_2_1_3 : RadiusFivePruning.patch4_2_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0965, parentRow_mem0965, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0965_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_1_3]
  rfl
theorem row_eq4_2_1_4 : RadiusFivePruning.stateRow4_2_1_4 = ParentOwnership.parentRow0865 := by rfl
theorem patch_mem4_2_1_4 : RadiusFivePruning.patch4_2_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0865, parentRow_mem0865, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0865_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_1_4]
  rfl
theorem row_eq4_2_1_5 : RadiusFivePruning.stateRow4_2_1_5 = ParentOwnership.parentRow0397 := by rfl
theorem patch_mem4_2_1_5 : RadiusFivePruning.patch4_2_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0397, parentRow_mem0397, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0397_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_1_5]
  rfl
theorem row_eq4_2_1_6 : RadiusFivePruning.stateRow4_2_1_6 = ParentOwnership.parentRow0864 := by rfl
theorem patch_mem4_2_1_6 : RadiusFivePruning.patch4_2_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0864, parentRow_mem0864, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0864_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_1_6]
  rfl
theorem row_eq4_2_1_7 : RadiusFivePruning.stateRow4_2_1_7 = ParentOwnership.parentRow0962 := by rfl
theorem patch_mem4_2_1_7 : RadiusFivePruning.patch4_2_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0962, parentRow_mem0962, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0962_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_1_7]
  rfl
theorem row_eq4_2_1_8 : RadiusFivePruning.stateRow4_2_1_8 = ParentOwnership.parentRow0964 := by rfl
theorem patch_mem4_2_1_8 : RadiusFivePruning.patch4_2_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0964, parentRow_mem0964, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0964_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_1_8]
  rfl
theorem row_eq4_2_1_10 : RadiusFivePruning.stateRow4_2_1_10 = ParentOwnership.parentRow0866 := by rfl
theorem patch_mem4_2_1_10 : RadiusFivePruning.patch4_2_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0866, parentRow_mem0866, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0866_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_1_10]
  rfl
theorem chunk_mem4_2_1 : ∀ p ∈ RadiusFivePruning.final4_2_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_2_1, List.forall_mem_cons]
  exact ⟨patch_mem4_2_1_0,⟨patch_mem4_2_1_1,⟨patch_mem4_2_1_3,⟨patch_mem4_2_1_4,⟨patch_mem4_2_1_5,⟨patch_mem4_2_1_6,⟨patch_mem4_2_1_7,⟨patch_mem4_2_1_8,⟨patch_mem4_2_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_2_2_0 : RadiusFivePruning.stateRow4_2_2_0 = ParentOwnership.parentRow1482 := by rfl
theorem patch_mem4_2_2_0 : RadiusFivePruning.patch4_2_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1482, parentRow_mem1482, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1482_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_2_0]
  rfl
theorem row_eq4_2_2_1 : RadiusFivePruning.stateRow4_2_2_1 = ParentOwnership.parentRow1481 := by rfl
theorem patch_mem4_2_2_1 : RadiusFivePruning.patch4_2_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1481, parentRow_mem1481, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1481_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_2_1]
  rfl
theorem row_eq4_2_2_2 : RadiusFivePruning.stateRow4_2_2_2 = ParentOwnership.parentRow1480 := by rfl
theorem patch_mem4_2_2_2 : RadiusFivePruning.patch4_2_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1480, parentRow_mem1480, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1480_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_2_2]
  rfl
theorem row_eq4_2_2_4 : RadiusFivePruning.stateRow4_2_2_4 = ParentOwnership.parentRow1479 := by rfl
theorem patch_mem4_2_2_4 : RadiusFivePruning.patch4_2_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1479, parentRow_mem1479, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1479_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_2_4]
  rfl
theorem row_eq4_2_2_6 : RadiusFivePruning.stateRow4_2_2_6 = ParentOwnership.parentRow1518 := by rfl
theorem patch_mem4_2_2_6 : RadiusFivePruning.patch4_2_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1518, parentRow_mem1518, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1518_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_2_6]
  rfl
theorem row_eq4_2_2_7 : RadiusFivePruning.stateRow4_2_2_7 = ParentOwnership.parentRow1521 := by rfl
theorem patch_mem4_2_2_7 : RadiusFivePruning.patch4_2_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1521, parentRow_mem1521, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1521_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_2_7]
  rfl
theorem row_eq4_2_2_9 : RadiusFivePruning.stateRow4_2_2_9 = ParentOwnership.parentRow2039 := by rfl
theorem patch_mem4_2_2_9 : RadiusFivePruning.patch4_2_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2039, parentRow_mem2039, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2039_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_2_9]
  rfl
theorem row_eq4_2_2_10 : RadiusFivePruning.stateRow4_2_2_10 = ParentOwnership.parentRow0784 := by rfl
theorem patch_mem4_2_2_10 : RadiusFivePruning.patch4_2_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0784, parentRow_mem0784, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0784_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_2_10]
  rfl
theorem row_eq4_2_2_11 : RadiusFivePruning.stateRow4_2_2_11 = ParentOwnership.parentRow0788 := by rfl
theorem patch_mem4_2_2_11 : RadiusFivePruning.patch4_2_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0788, parentRow_mem0788, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0788_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_2_11]
  rfl
theorem chunk_mem4_2_2 : ∀ p ∈ RadiusFivePruning.final4_2_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_2_2, List.forall_mem_cons]
  exact ⟨patch_mem4_2_2_0,⟨patch_mem4_2_2_1,⟨patch_mem4_2_2_2,⟨patch_mem4_2_2_4,⟨patch_mem4_2_2_6,⟨patch_mem4_2_2_7,⟨patch_mem4_2_2_9,⟨patch_mem4_2_2_10,⟨patch_mem4_2_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_2_3_0 : RadiusFivePruning.stateRow4_2_3_0 = ParentOwnership.parentRow2035 := by rfl
theorem patch_mem4_2_3_0 : RadiusFivePruning.patch4_2_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2035, parentRow_mem2035, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2035_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_3_0]
  rfl
theorem row_eq4_2_3_1 : RadiusFivePruning.stateRow4_2_3_1 = ParentOwnership.parentRow2038 := by rfl
theorem patch_mem4_2_3_1 : RadiusFivePruning.patch4_2_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2038, parentRow_mem2038, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2038_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_3_1]
  rfl
theorem row_eq4_2_3_2 : RadiusFivePruning.stateRow4_2_3_2 = ParentOwnership.parentRow1478 := by rfl
theorem patch_mem4_2_3_2 : RadiusFivePruning.patch4_2_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1478, parentRow_mem1478, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1478_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_3_2]
  rfl
theorem row_eq4_2_3_3 : RadiusFivePruning.stateRow4_2_3_3 = ParentOwnership.parentRow1519 := by rfl
theorem patch_mem4_2_3_3 : RadiusFivePruning.patch4_2_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1519, parentRow_mem1519, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1519_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_3_3]
  rfl
theorem row_eq4_2_3_4 : RadiusFivePruning.stateRow4_2_3_4 = ParentOwnership.parentRow1522 := by rfl
theorem patch_mem4_2_3_4 : RadiusFivePruning.patch4_2_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1522, parentRow_mem1522, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1522_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_3_4]
  rfl
theorem row_eq4_2_3_6 : RadiusFivePruning.stateRow4_2_3_6 = ParentOwnership.parentRow0785 := by rfl
theorem patch_mem4_2_3_6 : RadiusFivePruning.patch4_2_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0785, parentRow_mem0785, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0785_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_3_6]
  rfl
theorem row_eq4_2_3_7 : RadiusFivePruning.stateRow4_2_3_7 = ParentOwnership.parentRow0789 := by rfl
theorem patch_mem4_2_3_7 : RadiusFivePruning.patch4_2_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0789, parentRow_mem0789, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0789_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_3_7]
  rfl
theorem row_eq4_2_3_9 : RadiusFivePruning.stateRow4_2_3_9 = ParentOwnership.parentRow1477 := by rfl
theorem patch_mem4_2_3_9 : RadiusFivePruning.patch4_2_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1477, parentRow_mem1477, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1477_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_2_3_9]
  rfl
theorem chunk_mem4_2_3 : ∀ p ∈ RadiusFivePruning.final4_2_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_2_3, List.forall_mem_cons]
  exact ⟨patch_mem4_2_3_0,⟨patch_mem4_2_3_1,⟨patch_mem4_2_3_2,⟨patch_mem4_2_3_3,⟨patch_mem4_2_3_4,⟨patch_mem4_2_3_6,⟨patch_mem4_2_3_7,⟨patch_mem4_2_3_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
