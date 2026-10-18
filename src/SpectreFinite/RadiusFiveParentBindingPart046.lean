module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock7T3C7
public import SpectreFinite.RadiusFivePruningLiteralBlock7T3C8
public import SpectreFinite.RadiusFivePruningLiteralBlock7T4C0
public import SpectreFinite.RadiusFivePruningLiteralBlock7T4C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq7_3_7_0 : RadiusFivePruning.stateRow7_3_7_0 = ParentOwnership.parentRow0037 := by rfl
theorem patch_mem7_3_7_0 : RadiusFivePruning.patch7_3_7_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0037, parentRow_mem0037, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0037_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_7_0]
  rfl
theorem row_eq7_3_7_1 : RadiusFivePruning.stateRow7_3_7_1 = ParentOwnership.parentRow1233 := by rfl
theorem patch_mem7_3_7_1 : RadiusFivePruning.patch7_3_7_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1233, parentRow_mem1233, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1233_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_7_1]
  rfl
theorem row_eq7_3_7_2 : RadiusFivePruning.stateRow7_3_7_2 = ParentOwnership.parentRow1247 := by rfl
theorem patch_mem7_3_7_2 : RadiusFivePruning.patch7_3_7_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1247, parentRow_mem1247, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1247_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_7_2]
  rfl
theorem row_eq7_3_7_3 : RadiusFivePruning.stateRow7_3_7_3 = ParentOwnership.parentRow1234 := by rfl
theorem patch_mem7_3_7_3 : RadiusFivePruning.patch7_3_7_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1234, parentRow_mem1234, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1234_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_7_3]
  rfl
theorem row_eq7_3_7_4 : RadiusFivePruning.stateRow7_3_7_4 = ParentOwnership.parentRow1250 := by rfl
theorem patch_mem7_3_7_4 : RadiusFivePruning.patch7_3_7_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1250, parentRow_mem1250, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1250_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_7_4]
  rfl
theorem row_eq7_3_7_5 : RadiusFivePruning.stateRow7_3_7_5 = ParentOwnership.parentRow0048 := by rfl
theorem patch_mem7_3_7_5 : RadiusFivePruning.patch7_3_7_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0048, parentRow_mem0048, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0048_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_7_5]
  rfl
theorem row_eq7_3_7_6 : RadiusFivePruning.stateRow7_3_7_6 = ParentOwnership.parentRow1246 := by rfl
theorem patch_mem7_3_7_6 : RadiusFivePruning.patch7_3_7_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1246, parentRow_mem1246, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1246_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_7_6]
  rfl
theorem row_eq7_3_7_11 : RadiusFivePruning.stateRow7_3_7_11 = ParentOwnership.parentRow1241 := by rfl
theorem patch_mem7_3_7_11 : RadiusFivePruning.patch7_3_7_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1241, parentRow_mem1241, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1241_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_7_11]
  rfl
theorem chunk_mem7_3_7 : ∀ p ∈ RadiusFivePruning.final7_3_7, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_3_7, List.forall_mem_cons]
  exact ⟨patch_mem7_3_7_0,⟨patch_mem7_3_7_1,⟨patch_mem7_3_7_2,⟨patch_mem7_3_7_3,⟨patch_mem7_3_7_4,⟨patch_mem7_3_7_5,⟨patch_mem7_3_7_6,⟨patch_mem7_3_7_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_3_8_0 : RadiusFivePruning.stateRow7_3_8_0 = ParentOwnership.parentRow1229 := by rfl
theorem patch_mem7_3_8_0 : RadiusFivePruning.patch7_3_8_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1229, parentRow_mem1229, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1229_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_8_0]
  rfl
theorem row_eq7_3_8_1 : RadiusFivePruning.stateRow7_3_8_1 = ParentOwnership.parentRow1231 := by rfl
theorem patch_mem7_3_8_1 : RadiusFivePruning.patch7_3_8_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1231, parentRow_mem1231, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1231_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_8_1]
  rfl
theorem row_eq7_3_8_2 : RadiusFivePruning.stateRow7_3_8_2 = ParentOwnership.parentRow0039 := by rfl
theorem patch_mem7_3_8_2 : RadiusFivePruning.patch7_3_8_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0039, parentRow_mem0039, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0039_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_8_2]
  rfl
theorem row_eq7_3_8_3 : RadiusFivePruning.stateRow7_3_8_3 = ParentOwnership.parentRow1228 := by rfl
theorem patch_mem7_3_8_3 : RadiusFivePruning.patch7_3_8_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1228, parentRow_mem1228, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1228_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_8_3]
  rfl
theorem row_eq7_3_8_5 : RadiusFivePruning.stateRow7_3_8_5 = ParentOwnership.parentRow0047 := by rfl
theorem patch_mem7_3_8_5 : RadiusFivePruning.patch7_3_8_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0047, parentRow_mem0047, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0047_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_8_5]
  rfl
theorem row_eq7_3_8_7 : RadiusFivePruning.stateRow7_3_8_7 = ParentOwnership.parentRow0481 := by rfl
theorem patch_mem7_3_8_7 : RadiusFivePruning.patch7_3_8_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0481, parentRow_mem0481, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0481_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_8_7]
  rfl
theorem row_eq7_3_8_8 : RadiusFivePruning.stateRow7_3_8_8 = ParentOwnership.parentRow0049 := by rfl
theorem patch_mem7_3_8_8 : RadiusFivePruning.patch7_3_8_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0049, parentRow_mem0049, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0049_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_8_8]
  rfl
theorem row_eq7_3_8_9 : RadiusFivePruning.stateRow7_3_8_9 = ParentOwnership.parentRow0050 := by rfl
theorem patch_mem7_3_8_9 : RadiusFivePruning.patch7_3_8_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0050, parentRow_mem0050, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0050_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_3_8_9]
  rfl
theorem chunk_mem7_3_8 : ∀ p ∈ RadiusFivePruning.final7_3_8, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_3_8, List.forall_mem_cons]
  exact ⟨patch_mem7_3_8_0,⟨patch_mem7_3_8_1,⟨patch_mem7_3_8_2,⟨patch_mem7_3_8_3,⟨patch_mem7_3_8_5,⟨patch_mem7_3_8_7,⟨patch_mem7_3_8_8,⟨patch_mem7_3_8_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_4_0_1 : RadiusFivePruning.stateRow7_4_0_1 = ParentOwnership.parentRow1857 := by rfl
theorem patch_mem7_4_0_1 : RadiusFivePruning.patch7_4_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1857, parentRow_mem1857, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1857_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_0_1]
  rfl
theorem row_eq7_4_0_2 : RadiusFivePruning.stateRow7_4_0_2 = ParentOwnership.parentRow0857 := by rfl
theorem patch_mem7_4_0_2 : RadiusFivePruning.patch7_4_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0857, parentRow_mem0857, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0857_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_0_2]
  rfl
theorem row_eq7_4_0_3 : RadiusFivePruning.stateRow7_4_0_3 = ParentOwnership.parentRow1855 := by rfl
theorem patch_mem7_4_0_3 : RadiusFivePruning.patch7_4_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1855, parentRow_mem1855, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1855_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_0_3]
  rfl
theorem row_eq7_4_0_4 : RadiusFivePruning.stateRow7_4_0_4 = ParentOwnership.parentRow0652 := by rfl
theorem patch_mem7_4_0_4 : RadiusFivePruning.patch7_4_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0652, parentRow_mem0652, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0652_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_0_4]
  rfl
theorem row_eq7_4_0_5 : RadiusFivePruning.stateRow7_4_0_5 = ParentOwnership.parentRow1725 := by rfl
theorem patch_mem7_4_0_5 : RadiusFivePruning.patch7_4_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1725, parentRow_mem1725, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1725_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_0_5]
  rfl
theorem row_eq7_4_0_6 : RadiusFivePruning.stateRow7_4_0_6 = ParentOwnership.parentRow0653 := by rfl
theorem patch_mem7_4_0_6 : RadiusFivePruning.patch7_4_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0653, parentRow_mem0653, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0653_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_0_6]
  rfl
theorem row_eq7_4_0_7 : RadiusFivePruning.stateRow7_4_0_7 = ParentOwnership.parentRow1726 := by rfl
theorem patch_mem7_4_0_7 : RadiusFivePruning.patch7_4_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1726, parentRow_mem1726, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1726_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_0_7]
  rfl
theorem row_eq7_4_0_8 : RadiusFivePruning.stateRow7_4_0_8 = ParentOwnership.parentRow0973 := by rfl
theorem patch_mem7_4_0_8 : RadiusFivePruning.patch7_4_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0973, parentRow_mem0973, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0973_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_0_8]
  rfl
theorem row_eq7_4_0_11 : RadiusFivePruning.stateRow7_4_0_11 = ParentOwnership.parentRow1859 := by rfl
theorem patch_mem7_4_0_11 : RadiusFivePruning.patch7_4_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1859, parentRow_mem1859, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1859_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_0_11]
  rfl
theorem chunk_mem7_4_0 : ∀ p ∈ RadiusFivePruning.final7_4_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_4_0, List.forall_mem_cons]
  exact ⟨patch_mem7_4_0_1,⟨patch_mem7_4_0_2,⟨patch_mem7_4_0_3,⟨patch_mem7_4_0_4,⟨patch_mem7_4_0_5,⟨patch_mem7_4_0_6,⟨patch_mem7_4_0_7,⟨patch_mem7_4_0_8,⟨patch_mem7_4_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq7_4_1_0 : RadiusFivePruning.stateRow7_4_1_0 = ParentOwnership.parentRow1860 := by rfl
theorem patch_mem7_4_1_0 : RadiusFivePruning.patch7_4_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1860, parentRow_mem1860, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1860_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_1_0]
  rfl
theorem row_eq7_4_1_2 : RadiusFivePruning.stateRow7_4_1_2 = ParentOwnership.parentRow0858 := by rfl
theorem patch_mem7_4_1_2 : RadiusFivePruning.patch7_4_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0858, parentRow_mem0858, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0858_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_1_2]
  rfl
theorem row_eq7_4_1_3 : RadiusFivePruning.stateRow7_4_1_3 = ParentOwnership.parentRow0854 := by rfl
theorem patch_mem7_4_1_3 : RadiusFivePruning.patch7_4_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0854, parentRow_mem0854, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0854_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_1_3]
  rfl
theorem row_eq7_4_1_4 : RadiusFivePruning.stateRow7_4_1_4 = ParentOwnership.parentRow1856 := by rfl
theorem patch_mem7_4_1_4 : RadiusFivePruning.patch7_4_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1856, parentRow_mem1856, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1856_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_1_4]
  rfl
theorem row_eq7_4_1_5 : RadiusFivePruning.stateRow7_4_1_5 = ParentOwnership.parentRow1854 := by rfl
theorem patch_mem7_4_1_5 : RadiusFivePruning.patch7_4_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1854, parentRow_mem1854, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1854_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_1_5]
  rfl
theorem row_eq7_4_1_6 : RadiusFivePruning.stateRow7_4_1_6 = ParentOwnership.parentRow0972 := by rfl
theorem patch_mem7_4_1_6 : RadiusFivePruning.patch7_4_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0972, parentRow_mem0972, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0972_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_1_6]
  rfl
theorem row_eq7_4_1_9 : RadiusFivePruning.stateRow7_4_1_9 = ParentOwnership.parentRow0974 := by rfl
theorem patch_mem7_4_1_9 : RadiusFivePruning.patch7_4_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0974, parentRow_mem0974, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0974_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_1_9]
  rfl
theorem row_eq7_4_1_10 : RadiusFivePruning.stateRow7_4_1_10 = ParentOwnership.parentRow0970 := by rfl
theorem patch_mem7_4_1_10 : RadiusFivePruning.patch7_4_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0970, parentRow_mem0970, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0970_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_1_10]
  rfl
theorem row_eq7_4_1_11 : RadiusFivePruning.stateRow7_4_1_11 = ParentOwnership.parentRow1861 := by rfl
theorem patch_mem7_4_1_11 : RadiusFivePruning.patch7_4_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1861, parentRow_mem1861, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1861_property.1, ← literalDomain_eq_hexRegion, ← row_eq7_4_1_11]
  rfl
theorem chunk_mem7_4_1 : ∀ p ∈ RadiusFivePruning.final7_4_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final7_4_1, List.forall_mem_cons]
  exact ⟨patch_mem7_4_1_0,⟨patch_mem7_4_1_2,⟨patch_mem7_4_1_3,⟨patch_mem7_4_1_4,⟨patch_mem7_4_1_5,⟨patch_mem7_4_1_6,⟨patch_mem7_4_1_9,⟨patch_mem7_4_1_10,⟨patch_mem7_4_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
