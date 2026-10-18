module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock7T3C3
public import SpectreFinite.RadiusFivePruningLiteralBlock7T3C4
public import SpectreFinite.RadiusFivePruningLiteralBlock7T3C5
public import SpectreFinite.RadiusFivePruningLiteralBlock7T3C6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq7_3_3_0 : RadiusFivePruning.stateRow7_3_3_0 = ParentOwnership.parentRow1189 := by rfl
theorem patch_mem7_3_3_0 : RadiusFivePruning.patch7_3_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1189, parentRow_mem1189, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1189_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_3_0]
  rfl
theorem row_eq7_3_3_1 : RadiusFivePruning.stateRow7_3_3_1 = ParentOwnership.parentRow1198 := by rfl
theorem patch_mem7_3_3_1 : RadiusFivePruning.patch7_3_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1198, parentRow_mem1198, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1198_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_3_1]
  rfl
theorem row_eq7_3_3_2 : RadiusFivePruning.stateRow7_3_3_2 = ParentOwnership.parentRow1191 := by rfl
theorem patch_mem7_3_3_2 : RadiusFivePruning.patch7_3_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1191, parentRow_mem1191, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1191_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_3_2]
  rfl
theorem row_eq7_3_3_3 : RadiusFivePruning.stateRow7_3_3_3 = ParentOwnership.parentRow1200 := by rfl
theorem patch_mem7_3_3_3 : RadiusFivePruning.patch7_3_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1200, parentRow_mem1200, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1200_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_3_3]
  rfl
theorem row_eq7_3_3_5 : RadiusFivePruning.stateRow7_3_3_5 = ParentOwnership.parentRow1140 := by rfl
theorem patch_mem7_3_3_5 : RadiusFivePruning.patch7_3_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1140, parentRow_mem1140, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1140_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_3_5]
  rfl
theorem row_eq7_3_3_6 : RadiusFivePruning.stateRow7_3_3_6 = ParentOwnership.parentRow0267 := by rfl
theorem patch_mem7_3_3_6 : RadiusFivePruning.patch7_3_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0267, parentRow_mem0267, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0267_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_3_6]
  rfl
theorem row_eq7_3_3_7 : RadiusFivePruning.stateRow7_3_3_7 = ParentOwnership.parentRow1193 := by rfl
theorem patch_mem7_3_3_7 : RadiusFivePruning.patch7_3_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1193, parentRow_mem1193, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1193_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_3_7]
  rfl
theorem row_eq7_3_3_8 : RadiusFivePruning.stateRow7_3_3_8 = ParentOwnership.parentRow1196 := by rfl
theorem patch_mem7_3_3_8 : RadiusFivePruning.patch7_3_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1196, parentRow_mem1196, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1196_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_3_8]
  rfl
theorem row_eq7_3_3_9 : RadiusFivePruning.stateRow7_3_3_9 = ParentOwnership.parentRow1137 := by rfl
theorem patch_mem7_3_3_9 : RadiusFivePruning.patch7_3_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1137, parentRow_mem1137, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1137_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_3_9]
  rfl
theorem row_eq7_3_3_10 : RadiusFivePruning.stateRow7_3_3_10 = ParentOwnership.parentRow0264 := by rfl
theorem patch_mem7_3_3_10 : RadiusFivePruning.patch7_3_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0264, parentRow_mem0264, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0264_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_3_10]
  rfl
theorem row_eq7_3_3_11 : RadiusFivePruning.stateRow7_3_3_11 = ParentOwnership.parentRow1139 := by rfl
theorem patch_mem7_3_3_11 : RadiusFivePruning.patch7_3_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1139, parentRow_mem1139, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1139_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_3_11]
  rfl
theorem chunk_mem7_3_3 : ∀ p ∈ RadiusFivePruning.final7_3_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_3_3, List.forall_mem_cons]
  exact ⟨patch_mem7_3_3_0,⟨patch_mem7_3_3_1,⟨patch_mem7_3_3_2,⟨patch_mem7_3_3_3,⟨patch_mem7_3_3_5,⟨patch_mem7_3_3_6,⟨patch_mem7_3_3_7,⟨patch_mem7_3_3_8,⟨patch_mem7_3_3_9,⟨patch_mem7_3_3_10,⟨patch_mem7_3_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_3_4_1 : RadiusFivePruning.stateRow7_3_4_1 = ParentOwnership.parentRow1171 := by rfl
theorem patch_mem7_3_4_1 : RadiusFivePruning.patch7_3_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1171, parentRow_mem1171, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1171_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_4_1]
  rfl
theorem row_eq7_3_4_2 : RadiusFivePruning.stateRow7_3_4_2 = ParentOwnership.parentRow0268 := by rfl
theorem patch_mem7_3_4_2 : RadiusFivePruning.patch7_3_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0268, parentRow_mem0268, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0268_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_4_2]
  rfl
theorem row_eq7_3_4_3 : RadiusFivePruning.stateRow7_3_4_3 = ParentOwnership.parentRow1194 := by rfl
theorem patch_mem7_3_4_3 : RadiusFivePruning.patch7_3_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1194, parentRow_mem1194, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1194_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_4_3]
  rfl
theorem row_eq7_3_4_4 : RadiusFivePruning.stateRow7_3_4_4 = ParentOwnership.parentRow1197 := by rfl
theorem patch_mem7_3_4_4 : RadiusFivePruning.patch7_3_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1197, parentRow_mem1197, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1197_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_4_4]
  rfl
theorem row_eq7_3_4_5 : RadiusFivePruning.stateRow7_3_4_5 = ParentOwnership.parentRow0265 := by rfl
theorem patch_mem7_3_4_5 : RadiusFivePruning.patch7_3_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0265, parentRow_mem0265, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0265_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_4_5]
  rfl
theorem row_eq7_3_4_8 : RadiusFivePruning.stateRow7_3_4_8 = ParentOwnership.parentRow0036 := by rfl
theorem patch_mem7_3_4_8 : RadiusFivePruning.patch7_3_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0036, parentRow_mem0036, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0036_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_4_8]
  rfl
theorem row_eq7_3_4_10 : RadiusFivePruning.stateRow7_3_4_10 = ParentOwnership.parentRow1141 := by rfl
theorem patch_mem7_3_4_10 : RadiusFivePruning.patch7_3_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1141, parentRow_mem1141, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1141_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_4_10]
  rfl
theorem chunk_mem7_3_4 : ∀ p ∈ RadiusFivePruning.final7_3_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_3_4, List.forall_mem_cons]
  exact ⟨patch_mem7_3_4_1,⟨patch_mem7_3_4_2,⟨patch_mem7_3_4_3,⟨patch_mem7_3_4_4,⟨patch_mem7_3_4_5,⟨patch_mem7_3_4_8,⟨patch_mem7_3_4_10,by simp⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_3_5_0 : RadiusFivePruning.stateRow7_3_5_0 = ParentOwnership.parentRow1195 := by rfl
theorem patch_mem7_3_5_0 : RadiusFivePruning.patch7_3_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1195, parentRow_mem1195, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1195_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_5_0]
  rfl
theorem row_eq7_3_5_2 : RadiusFivePruning.stateRow7_3_5_2 = ParentOwnership.parentRow1138 := by rfl
theorem patch_mem7_3_5_2 : RadiusFivePruning.patch7_3_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1138, parentRow_mem1138, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1138_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_5_2]
  rfl
theorem row_eq7_3_5_3 : RadiusFivePruning.stateRow7_3_5_3 = ParentOwnership.parentRow0266 := by rfl
theorem patch_mem7_3_5_3 : RadiusFivePruning.patch7_3_5_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0266, parentRow_mem0266, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0266_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_5_3]
  rfl
theorem row_eq7_3_5_4 : RadiusFivePruning.stateRow7_3_5_4 = ParentOwnership.parentRow1244 := by rfl
theorem patch_mem7_3_5_4 : RadiusFivePruning.patch7_3_5_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1244, parentRow_mem1244, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1244_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_5_4]
  rfl
theorem row_eq7_3_5_5 : RadiusFivePruning.stateRow7_3_5_5 = ParentOwnership.parentRow1242 := by rfl
theorem patch_mem7_3_5_5 : RadiusFivePruning.patch7_3_5_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1242, parentRow_mem1242, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1242_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_5_5]
  rfl
theorem row_eq7_3_5_6 : RadiusFivePruning.stateRow7_3_5_6 = ParentOwnership.parentRow1248 := by rfl
theorem patch_mem7_3_5_6 : RadiusFivePruning.patch7_3_5_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1248, parentRow_mem1248, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1248_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_5_6]
  rfl
theorem row_eq7_3_5_7 : RadiusFivePruning.stateRow7_3_5_7 = ParentOwnership.parentRow1239 := by rfl
theorem patch_mem7_3_5_7 : RadiusFivePruning.patch7_3_5_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1239, parentRow_mem1239, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1239_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_5_7]
  rfl
theorem row_eq7_3_5_8 : RadiusFivePruning.stateRow7_3_5_8 = ParentOwnership.parentRow1230 := by rfl
theorem patch_mem7_3_5_8 : RadiusFivePruning.patch7_3_5_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1230, parentRow_mem1230, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1230_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_5_8]
  rfl
theorem row_eq7_3_5_9 : RadiusFivePruning.stateRow7_3_5_9 = ParentOwnership.parentRow0038 := by rfl
theorem patch_mem7_3_5_9 : RadiusFivePruning.patch7_3_5_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0038, parentRow_mem0038, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0038_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_5_9]
  rfl
theorem row_eq7_3_5_10 : RadiusFivePruning.stateRow7_3_5_10 = ParentOwnership.parentRow1227 := by rfl
theorem patch_mem7_3_5_10 : RadiusFivePruning.patch7_3_5_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1227, parentRow_mem1227, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1227_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_5_10]
  rfl
theorem row_eq7_3_5_11 : RadiusFivePruning.stateRow7_3_5_11 = ParentOwnership.parentRow1245 := by rfl
theorem patch_mem7_3_5_11 : RadiusFivePruning.patch7_3_5_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1245, parentRow_mem1245, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1245_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_5_11]
  rfl
theorem chunk_mem7_3_5 : ∀ p ∈ RadiusFivePruning.final7_3_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_3_5, List.forall_mem_cons]
  exact ⟨patch_mem7_3_5_0,⟨patch_mem7_3_5_2,⟨patch_mem7_3_5_3,⟨patch_mem7_3_5_4,⟨patch_mem7_3_5_5,⟨patch_mem7_3_5_6,⟨patch_mem7_3_5_7,⟨patch_mem7_3_5_8,⟨patch_mem7_3_5_9,⟨patch_mem7_3_5_10,⟨patch_mem7_3_5_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_3_6_0 : RadiusFivePruning.stateRow7_3_6_0 = ParentOwnership.parentRow1243 := by rfl
theorem patch_mem7_3_6_0 : RadiusFivePruning.patch7_3_6_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1243, parentRow_mem1243, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1243_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_6_0]
  rfl
theorem row_eq7_3_6_1 : RadiusFivePruning.stateRow7_3_6_1 = ParentOwnership.parentRow1249 := by rfl
theorem patch_mem7_3_6_1 : RadiusFivePruning.patch7_3_6_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1249, parentRow_mem1249, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1249_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_6_1]
  rfl
theorem row_eq7_3_6_2 : RadiusFivePruning.stateRow7_3_6_2 = ParentOwnership.parentRow1240 := by rfl
theorem patch_mem7_3_6_2 : RadiusFivePruning.patch7_3_6_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1240, parentRow_mem1240, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1240_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_6_2]
  rfl
theorem row_eq7_3_6_4 : RadiusFivePruning.stateRow7_3_6_4 = ParentOwnership.parentRow1211 := by rfl
theorem patch_mem7_3_6_4 : RadiusFivePruning.patch7_3_6_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1211, parentRow_mem1211, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1211_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_6_4]
  rfl
theorem row_eq7_3_6_6 : RadiusFivePruning.stateRow7_3_6_6 = ParentOwnership.parentRow1210 := by rfl
theorem patch_mem7_3_6_6 : RadiusFivePruning.patch7_3_6_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1210, parentRow_mem1210, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1210_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_6_6]
  rfl
theorem row_eq7_3_6_7 : RadiusFivePruning.stateRow7_3_6_7 = ParentOwnership.parentRow1232 := by rfl
theorem patch_mem7_3_6_7 : RadiusFivePruning.patch7_3_6_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1232, parentRow_mem1232, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1232_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_6_7]
  rfl
theorem row_eq7_3_6_9 : RadiusFivePruning.stateRow7_3_6_9 = ParentOwnership.parentRow1218 := by rfl
theorem patch_mem7_3_6_9 : RadiusFivePruning.patch7_3_6_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1218, parentRow_mem1218, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1218_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_6_9]
  rfl
theorem row_eq7_3_6_10 : RadiusFivePruning.stateRow7_3_6_10 = ParentOwnership.parentRow1226 := by rfl
theorem patch_mem7_3_6_10 : RadiusFivePruning.patch7_3_6_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1226, parentRow_mem1226, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1226_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_6_10]
  rfl
theorem row_eq7_3_6_11 : RadiusFivePruning.stateRow7_3_6_11 = ParentOwnership.parentRow0035 := by rfl
theorem patch_mem7_3_6_11 : RadiusFivePruning.patch7_3_6_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0035, parentRow_mem0035, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0035_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_6_11]
  rfl
theorem chunk_mem7_3_6 : ∀ p ∈ RadiusFivePruning.final7_3_6, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_3_6, List.forall_mem_cons]
  exact ⟨patch_mem7_3_6_0,⟨patch_mem7_3_6_1,⟨patch_mem7_3_6_2,⟨patch_mem7_3_6_4,⟨patch_mem7_3_6_6,⟨patch_mem7_3_6_7,⟨patch_mem7_3_6_9,⟨patch_mem7_3_6_10,⟨patch_mem7_3_6_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
