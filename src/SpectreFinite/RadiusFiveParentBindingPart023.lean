module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock4T5C0
public import SpectreFinite.RadiusFivePruningLiteralBlock4T5C1
public import SpectreFinite.RadiusFivePruningLiteralBlock4T5C2
public import SpectreFinite.RadiusFivePruningLiteralBlock4T5C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq4_5_0_1 : RadiusFivePruning.stateRow4_5_0_1 = ParentOwnership.parentRow0441 := by rfl
theorem patch_mem4_5_0_1 : RadiusFivePruning.patch4_5_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0441, parentRow_mem0441, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0441_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_0_1]
  rfl
theorem row_eq4_5_0_3 : RadiusFivePruning.stateRow4_5_0_3 = ParentOwnership.parentRow0443 := by rfl
theorem patch_mem4_5_0_3 : RadiusFivePruning.patch4_5_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0443, parentRow_mem0443, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0443_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_0_3]
  rfl
theorem row_eq4_5_0_4 : RadiusFivePruning.stateRow4_5_0_4 = ParentOwnership.parentRow0450 := by rfl
theorem patch_mem4_5_0_4 : RadiusFivePruning.patch4_5_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0450, parentRow_mem0450, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0450_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_0_4]
  rfl
theorem row_eq4_5_0_6 : RadiusFivePruning.stateRow4_5_0_6 = ParentOwnership.parentRow0444 := by rfl
theorem patch_mem4_5_0_6 : RadiusFivePruning.patch4_5_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0444, parentRow_mem0444, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0444_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_0_6]
  rfl
theorem row_eq4_5_0_7 : RadiusFivePruning.stateRow4_5_0_7 = ParentOwnership.parentRow0446 := by rfl
theorem patch_mem4_5_0_7 : RadiusFivePruning.patch4_5_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0446, parentRow_mem0446, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0446_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_0_7]
  rfl
theorem row_eq4_5_0_9 : RadiusFivePruning.stateRow4_5_0_9 = ParentOwnership.parentRow0445 := by rfl
theorem patch_mem4_5_0_9 : RadiusFivePruning.patch4_5_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0445, parentRow_mem0445, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0445_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_0_9]
  rfl
theorem row_eq4_5_0_10 : RadiusFivePruning.stateRow4_5_0_10 = ParentOwnership.parentRow0447 := by rfl
theorem patch_mem4_5_0_10 : RadiusFivePruning.patch4_5_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0447, parentRow_mem0447, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0447_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_0_10]
  rfl
theorem row_eq4_5_0_11 : RadiusFivePruning.stateRow4_5_0_11 = ParentOwnership.parentRow0442 := by rfl
theorem patch_mem4_5_0_11 : RadiusFivePruning.patch4_5_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0442, parentRow_mem0442, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0442_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_0_11]
  rfl
theorem chunk_mem4_5_0 : ∀ p ∈ RadiusFivePruning.final4_5_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_5_0, List.forall_mem_cons]
  exact ⟨patch_mem4_5_0_1,⟨patch_mem4_5_0_3,⟨patch_mem4_5_0_4,⟨patch_mem4_5_0_6,⟨patch_mem4_5_0_7,⟨patch_mem4_5_0_9,⟨patch_mem4_5_0_10,⟨patch_mem4_5_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_5_1_0 : RadiusFivePruning.stateRow4_5_1_0 = ParentOwnership.parentRow0449 := by rfl
theorem patch_mem4_5_1_0 : RadiusFivePruning.patch4_5_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0449, parentRow_mem0449, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0449_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_1_0]
  rfl
theorem row_eq4_5_1_1 : RadiusFivePruning.stateRow4_5_1_1 = ParentOwnership.parentRow0452 := by rfl
theorem patch_mem4_5_1_1 : RadiusFivePruning.patch4_5_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0452, parentRow_mem0452, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0452_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_1_1]
  rfl
theorem row_eq4_5_1_3 : RadiusFivePruning.stateRow4_5_1_3 = ParentOwnership.parentRow0448 := by rfl
theorem patch_mem4_5_1_3 : RadiusFivePruning.patch4_5_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0448, parentRow_mem0448, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0448_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_1_3]
  rfl
theorem row_eq4_5_1_4 : RadiusFivePruning.stateRow4_5_1_4 = ParentOwnership.parentRow0451 := by rfl
theorem patch_mem4_5_1_4 : RadiusFivePruning.patch4_5_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0451, parentRow_mem0451, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0451_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_1_4]
  rfl
theorem row_eq4_5_1_5 : RadiusFivePruning.stateRow4_5_1_5 = ParentOwnership.parentRow0435 := by rfl
theorem patch_mem4_5_1_5 : RadiusFivePruning.patch4_5_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0435, parentRow_mem0435, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0435_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_1_5]
  rfl
theorem row_eq4_5_1_6 : RadiusFivePruning.stateRow4_5_1_6 = ParentOwnership.parentRow0437 := by rfl
theorem patch_mem4_5_1_6 : RadiusFivePruning.patch4_5_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0437, parentRow_mem0437, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0437_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_1_6]
  rfl
theorem row_eq4_5_1_7 : RadiusFivePruning.stateRow4_5_1_7 = ParentOwnership.parentRow0436 := by rfl
theorem patch_mem4_5_1_7 : RadiusFivePruning.patch4_5_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0436, parentRow_mem0436, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0436_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_1_7]
  rfl
theorem row_eq4_5_1_8 : RadiusFivePruning.stateRow4_5_1_8 = ParentOwnership.parentRow0439 := by rfl
theorem patch_mem4_5_1_8 : RadiusFivePruning.patch4_5_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0439, parentRow_mem0439, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0439_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_1_8]
  rfl
theorem row_eq4_5_1_10 : RadiusFivePruning.stateRow4_5_1_10 = ParentOwnership.parentRow0438 := by rfl
theorem patch_mem4_5_1_10 : RadiusFivePruning.patch4_5_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0438, parentRow_mem0438, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0438_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_1_10]
  rfl
theorem chunk_mem4_5_1 : ∀ p ∈ RadiusFivePruning.final4_5_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_5_1, List.forall_mem_cons]
  exact ⟨patch_mem4_5_1_0,⟨patch_mem4_5_1_1,⟨patch_mem4_5_1_3,⟨patch_mem4_5_1_4,⟨patch_mem4_5_1_5,⟨patch_mem4_5_1_6,⟨patch_mem4_5_1_7,⟨patch_mem4_5_1_8,⟨patch_mem4_5_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_5_2_0 : RadiusFivePruning.stateRow4_5_2_0 = ParentOwnership.parentRow1132 := by rfl
theorem patch_mem4_5_2_0 : RadiusFivePruning.patch4_5_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1132, parentRow_mem1132, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1132_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_2_0]
  rfl
theorem row_eq4_5_2_1 : RadiusFivePruning.stateRow4_5_2_1 = ParentOwnership.parentRow0263 := by rfl
theorem patch_mem4_5_2_1 : RadiusFivePruning.patch4_5_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0263, parentRow_mem0263, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0263_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_2_1]
  rfl
theorem row_eq4_5_2_2 : RadiusFivePruning.stateRow4_5_2_2 = ParentOwnership.parentRow1133 := by rfl
theorem patch_mem4_5_2_2 : RadiusFivePruning.patch4_5_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1133, parentRow_mem1133, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1133_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_2_2]
  rfl
theorem row_eq4_5_2_4 : RadiusFivePruning.stateRow4_5_2_4 = ParentOwnership.parentRow0256 := by rfl
theorem patch_mem4_5_2_4 : RadiusFivePruning.patch4_5_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0256, parentRow_mem0256, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0256_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_2_4]
  rfl
theorem row_eq4_5_2_6 : RadiusFivePruning.stateRow4_5_2_6 = ParentOwnership.parentRow1161 := by rfl
theorem patch_mem4_5_2_6 : RadiusFivePruning.patch4_5_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1161, parentRow_mem1161, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1161_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_2_6]
  rfl
theorem row_eq4_5_2_7 : RadiusFivePruning.stateRow4_5_2_7 = ParentOwnership.parentRow1162 := by rfl
theorem patch_mem4_5_2_7 : RadiusFivePruning.patch4_5_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1162, parentRow_mem1162, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1162_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_2_7]
  rfl
theorem row_eq4_5_2_9 : RadiusFivePruning.stateRow4_5_2_9 = ParentOwnership.parentRow0007 := by rfl
theorem patch_mem4_5_2_9 : RadiusFivePruning.patch4_5_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0007, parentRow_mem0007, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0007_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_2_9]
  rfl
theorem row_eq4_5_2_10 : RadiusFivePruning.stateRow4_5_2_10 = ParentOwnership.parentRow1163 := by rfl
theorem patch_mem4_5_2_10 : RadiusFivePruning.patch4_5_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1163, parentRow_mem1163, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1163_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_2_10]
  rfl
theorem row_eq4_5_2_11 : RadiusFivePruning.stateRow4_5_2_11 = ParentOwnership.parentRow1159 := by rfl
theorem patch_mem4_5_2_11 : RadiusFivePruning.patch4_5_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1159, parentRow_mem1159, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1159_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_2_11]
  rfl
theorem chunk_mem4_5_2 : ∀ p ∈ RadiusFivePruning.final4_5_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_5_2, List.forall_mem_cons]
  exact ⟨patch_mem4_5_2_0,⟨patch_mem4_5_2_1,⟨patch_mem4_5_2_2,⟨patch_mem4_5_2_4,⟨patch_mem4_5_2_6,⟨patch_mem4_5_2_7,⟨patch_mem4_5_2_9,⟨patch_mem4_5_2_10,⟨patch_mem4_5_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_5_3_0 : RadiusFivePruning.stateRow4_5_3_0 = ParentOwnership.parentRow1164 := by rfl
theorem patch_mem4_5_3_0 : RadiusFivePruning.patch4_5_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1164, parentRow_mem1164, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1164_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_3_0]
  rfl
theorem row_eq4_5_3_1 : RadiusFivePruning.stateRow4_5_3_1 = ParentOwnership.parentRow1160 := by rfl
theorem patch_mem4_5_3_1 : RadiusFivePruning.patch4_5_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1160, parentRow_mem1160, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1160_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_3_1]
  rfl
theorem row_eq4_5_3_2 : RadiusFivePruning.stateRow4_5_3_2 = ParentOwnership.parentRow1165 := by rfl
theorem patch_mem4_5_3_2 : RadiusFivePruning.patch4_5_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1165, parentRow_mem1165, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1165_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_3_2]
  rfl
theorem row_eq4_5_3_3 : RadiusFivePruning.stateRow4_5_3_3 = ParentOwnership.parentRow1167 := by rfl
theorem patch_mem4_5_3_3 : RadiusFivePruning.patch4_5_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1167, parentRow_mem1167, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1167_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_3_3]
  rfl
theorem row_eq4_5_3_4 : RadiusFivePruning.stateRow4_5_3_4 = ParentOwnership.parentRow1168 := by rfl
theorem patch_mem4_5_3_4 : RadiusFivePruning.patch4_5_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1168, parentRow_mem1168, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1168_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_3_4]
  rfl
theorem row_eq4_5_3_6 : RadiusFivePruning.stateRow4_5_3_6 = ParentOwnership.parentRow1169 := by rfl
theorem patch_mem4_5_3_6 : RadiusFivePruning.patch4_5_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1169, parentRow_mem1169, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1169_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_3_6]
  rfl
theorem row_eq4_5_3_7 : RadiusFivePruning.stateRow4_5_3_7 = ParentOwnership.parentRow1166 := by rfl
theorem patch_mem4_5_3_7 : RadiusFivePruning.patch4_5_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1166, parentRow_mem1166, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1166_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_3_7]
  rfl
theorem row_eq4_5_3_9 : RadiusFivePruning.stateRow4_5_3_9 = ParentOwnership.parentRow1182 := by rfl
theorem patch_mem4_5_3_9 : RadiusFivePruning.patch4_5_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1182, parentRow_mem1182, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1182_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_5_3_9]
  rfl
theorem chunk_mem4_5_3 : ∀ p ∈ RadiusFivePruning.final4_5_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_5_3, List.forall_mem_cons]
  exact ⟨patch_mem4_5_3_0,⟨patch_mem4_5_3_1,⟨patch_mem4_5_3_2,⟨patch_mem4_5_3_3,⟨patch_mem4_5_3_4,⟨patch_mem4_5_3_6,⟨patch_mem4_5_3_7,⟨patch_mem4_5_3_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
