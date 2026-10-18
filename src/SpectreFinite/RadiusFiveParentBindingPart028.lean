module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock5T5C1
public import SpectreFinite.RadiusFivePruningLiteralBlock5T5C2
public import SpectreFinite.RadiusFivePruningLiteralBlock6T0C0
public import SpectreFinite.RadiusFivePruningLiteralBlock6T0C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq5_5_1_0 : RadiusFivePruning.stateRow5_5_1_0 = ParentOwnership.parentRow0379 := by rfl
theorem patch_mem5_5_1_0 : RadiusFivePruning.patch5_5_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0379, parentRow_mem0379, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0379_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_1_0]
  rfl
theorem row_eq5_5_1_1 : RadiusFivePruning.stateRow5_5_1_1 = ParentOwnership.parentRow0229 := by rfl
theorem patch_mem5_5_1_1 : RadiusFivePruning.patch5_5_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0229, parentRow_mem0229, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0229_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_1_1]
  rfl
theorem row_eq5_5_1_3 : RadiusFivePruning.stateRow5_5_1_3 = ParentOwnership.parentRow0224 := by rfl
theorem patch_mem5_5_1_3 : RadiusFivePruning.patch5_5_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0224, parentRow_mem0224, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0224_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_1_3]
  rfl
theorem row_eq5_5_1_4 : RadiusFivePruning.stateRow5_5_1_4 = ParentOwnership.parentRow0372 := by rfl
theorem patch_mem5_5_1_4 : RadiusFivePruning.patch5_5_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0372, parentRow_mem0372, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0372_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_1_4]
  rfl
theorem row_eq5_5_1_7 : RadiusFivePruning.stateRow5_5_1_7 = ParentOwnership.parentRow0381 := by rfl
theorem patch_mem5_5_1_7 : RadiusFivePruning.patch5_5_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0381, parentRow_mem0381, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0381_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_1_7]
  rfl
theorem row_eq5_5_1_8 : RadiusFivePruning.stateRow5_5_1_8 = ParentOwnership.parentRow0380 := by rfl
theorem patch_mem5_5_1_8 : RadiusFivePruning.patch5_5_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0380, parentRow_mem0380, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0380_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_1_8]
  rfl
theorem row_eq5_5_1_9 : RadiusFivePruning.stateRow5_5_1_9 = ParentOwnership.parentRow1498 := by rfl
theorem patch_mem5_5_1_9 : RadiusFivePruning.patch5_5_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1498, parentRow_mem1498, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1498_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_1_9]
  rfl
theorem row_eq5_5_1_11 : RadiusFivePruning.stateRow5_5_1_11 = ParentOwnership.parentRow0382 := by rfl
theorem patch_mem5_5_1_11 : RadiusFivePruning.patch5_5_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0382, parentRow_mem0382, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0382_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_1_11]
  rfl
theorem chunk_mem5_5_1 : ∀ p ∈ RadiusFivePruning.final5_5_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_5_1, List.forall_mem_cons]
  exact ⟨patch_mem5_5_1_0,⟨patch_mem5_5_1_1,⟨patch_mem5_5_1_3,⟨patch_mem5_5_1_4,⟨patch_mem5_5_1_7,⟨patch_mem5_5_1_8,⟨patch_mem5_5_1_9,⟨patch_mem5_5_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq5_5_2_0 : RadiusFivePruning.stateRow5_5_2_0 = ParentOwnership.parentRow1470 := by rfl
theorem patch_mem5_5_2_0 : RadiusFivePruning.patch5_5_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1470, parentRow_mem1470, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1470_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_2_0]
  rfl
theorem row_eq5_5_2_1 : RadiusFivePruning.stateRow5_5_2_1 = ParentOwnership.parentRow1471 := by rfl
theorem patch_mem5_5_2_1 : RadiusFivePruning.patch5_5_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1471, parentRow_mem1471, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1471_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_2_1]
  rfl
theorem row_eq5_5_2_2 : RadiusFivePruning.stateRow5_5_2_2 = ParentOwnership.parentRow0237 := by rfl
theorem patch_mem5_5_2_2 : RadiusFivePruning.patch5_5_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0237, parentRow_mem0237, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0237_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_2_2]
  rfl
theorem row_eq5_5_2_3 : RadiusFivePruning.stateRow5_5_2_3 = ParentOwnership.parentRow0245 := by rfl
theorem patch_mem5_5_2_3 : RadiusFivePruning.patch5_5_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0245, parentRow_mem0245, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0245_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_2_3]
  rfl
theorem row_eq5_5_2_4 : RadiusFivePruning.stateRow5_5_2_4 = ParentOwnership.parentRow0401 := by rfl
theorem patch_mem5_5_2_4 : RadiusFivePruning.patch5_5_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0401, parentRow_mem0401, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0401_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_2_4]
  rfl
theorem row_eq5_5_2_5 : RadiusFivePruning.stateRow5_5_2_5 = ParentOwnership.parentRow0400 := by rfl
theorem patch_mem5_5_2_5 : RadiusFivePruning.patch5_5_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0400, parentRow_mem0400, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0400_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_2_5]
  rfl
theorem row_eq5_5_2_6 : RadiusFivePruning.stateRow5_5_2_6 = ParentOwnership.parentRow0238 := by rfl
theorem patch_mem5_5_2_6 : RadiusFivePruning.patch5_5_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0238, parentRow_mem0238, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0238_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_2_6]
  rfl
theorem row_eq5_5_2_7 : RadiusFivePruning.stateRow5_5_2_7 = ParentOwnership.parentRow0246 := by rfl
theorem patch_mem5_5_2_7 : RadiusFivePruning.patch5_5_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0246, parentRow_mem0246, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0246_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_2_7]
  rfl
theorem row_eq5_5_2_8 : RadiusFivePruning.stateRow5_5_2_8 = ParentOwnership.parentRow0403 := by rfl
theorem patch_mem5_5_2_8 : RadiusFivePruning.patch5_5_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0403, parentRow_mem0403, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0403_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_2_8]
  rfl
theorem row_eq5_5_2_9 : RadiusFivePruning.stateRow5_5_2_9 = ParentOwnership.parentRow0402 := by rfl
theorem patch_mem5_5_2_9 : RadiusFivePruning.patch5_5_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0402, parentRow_mem0402, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0402_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_2_9]
  rfl
theorem row_eq5_5_2_10 : RadiusFivePruning.stateRow5_5_2_10 = ParentOwnership.parentRow0230 := by rfl
theorem patch_mem5_5_2_10 : RadiusFivePruning.patch5_5_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0230, parentRow_mem0230, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0230_property.1, ← literalDomain_eq_hexRegion, ← row_eq5_5_2_10]
  rfl
theorem chunk_mem5_5_2 : ∀ p ∈ RadiusFivePruning.final5_5_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final5_5_2, List.forall_mem_cons]
  exact ⟨patch_mem5_5_2_0,⟨patch_mem5_5_2_1,⟨patch_mem5_5_2_2,⟨patch_mem5_5_2_3,⟨patch_mem5_5_2_4,⟨patch_mem5_5_2_5,⟨patch_mem5_5_2_6,⟨patch_mem5_5_2_7,⟨patch_mem5_5_2_8,⟨patch_mem5_5_2_9,⟨patch_mem5_5_2_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq6_0_0_2 : RadiusFivePruning.stateRow6_0_0_2 = ParentOwnership.parentRow1920 := by rfl
theorem patch_mem6_0_0_2 : RadiusFivePruning.patch6_0_0_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1920, parentRow_mem1920, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1920_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_0_2]
  rfl
theorem row_eq6_0_0_3 : RadiusFivePruning.stateRow6_0_0_3 = ParentOwnership.parentRow1937 := by rfl
theorem patch_mem6_0_0_3 : RadiusFivePruning.patch6_0_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1937, parentRow_mem1937, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1937_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_0_3]
  rfl
theorem row_eq6_0_0_5 : RadiusFivePruning.stateRow6_0_0_5 = ParentOwnership.parentRow1939 := by rfl
theorem patch_mem6_0_0_5 : RadiusFivePruning.patch6_0_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1939, parentRow_mem1939, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1939_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_0_5]
  rfl
theorem row_eq6_0_0_6 : RadiusFivePruning.stateRow6_0_0_6 = ParentOwnership.parentRow1940 := by rfl
theorem patch_mem6_0_0_6 : RadiusFivePruning.patch6_0_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1940, parentRow_mem1940, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1940_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_0_6]
  rfl
theorem row_eq6_0_0_8 : RadiusFivePruning.stateRow6_0_0_8 = ParentOwnership.parentRow1891 := by rfl
theorem patch_mem6_0_0_8 : RadiusFivePruning.patch6_0_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1891, parentRow_mem1891, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1891_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_0_8]
  rfl
theorem row_eq6_0_0_10 : RadiusFivePruning.stateRow6_0_0_10 = ParentOwnership.parentRow1898 := by rfl
theorem patch_mem6_0_0_10 : RadiusFivePruning.patch6_0_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1898, parentRow_mem1898, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1898_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_0_10]
  rfl
theorem chunk_mem6_0_0 : ∀ p ∈ RadiusFivePruning.final6_0_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_0_0, List.forall_mem_cons]
  exact ⟨patch_mem6_0_0_2,⟨patch_mem6_0_0_3,⟨patch_mem6_0_0_5,⟨patch_mem6_0_0_6,⟨patch_mem6_0_0_8,⟨patch_mem6_0_0_10,by simp⟩⟩⟩⟩⟩⟩
theorem row_eq6_0_1_0 : RadiusFivePruning.stateRow6_0_1_0 = ParentOwnership.parentRow1899 := by rfl
theorem patch_mem6_0_1_0 : RadiusFivePruning.patch6_0_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1899, parentRow_mem1899, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1899_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_1_0]
  rfl
theorem row_eq6_0_1_3 : RadiusFivePruning.stateRow6_0_1_3 = ParentOwnership.parentRow1911 := by rfl
theorem patch_mem6_0_1_3 : RadiusFivePruning.patch6_0_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1911, parentRow_mem1911, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1911_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_1_3]
  rfl
theorem row_eq6_0_1_4 : RadiusFivePruning.stateRow6_0_1_4 = ParentOwnership.parentRow1912 := by rfl
theorem patch_mem6_0_1_4 : RadiusFivePruning.patch6_0_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1912, parentRow_mem1912, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1912_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_1_4]
  rfl
theorem row_eq6_0_1_5 : RadiusFivePruning.stateRow6_0_1_5 = ParentOwnership.parentRow1913 := by rfl
theorem patch_mem6_0_1_5 : RadiusFivePruning.patch6_0_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1913, parentRow_mem1913, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1913_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_1_5]
  rfl
theorem row_eq6_0_1_7 : RadiusFivePruning.stateRow6_0_1_7 = ParentOwnership.parentRow0688 := by rfl
theorem patch_mem6_0_1_7 : RadiusFivePruning.patch6_0_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0688, parentRow_mem0688, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0688_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_1_7]
  rfl
theorem row_eq6_0_1_8 : RadiusFivePruning.stateRow6_0_1_8 = ParentOwnership.parentRow0696 := by rfl
theorem patch_mem6_0_1_8 : RadiusFivePruning.patch6_0_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0696, parentRow_mem0696, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0696_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_1_8]
  rfl
theorem row_eq6_0_1_10 : RadiusFivePruning.stateRow6_0_1_10 = ParentOwnership.parentRow0697 := by rfl
theorem patch_mem6_0_1_10 : RadiusFivePruning.patch6_0_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0697, parentRow_mem0697, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0697_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_1_10]
  rfl
theorem row_eq6_0_1_11 : RadiusFivePruning.stateRow6_0_1_11 = ParentOwnership.parentRow0698 := by rfl
theorem patch_mem6_0_1_11 : RadiusFivePruning.patch6_0_1_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0698, parentRow_mem0698, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0698_property.1, ← literalDomain_eq_hexRegion, ← row_eq6_0_1_11]
  rfl
theorem chunk_mem6_0_1 : ∀ p ∈ RadiusFivePruning.final6_0_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final6_0_1, List.forall_mem_cons]
  exact ⟨patch_mem6_0_1_0,⟨patch_mem6_0_1_3,⟨patch_mem6_0_1_4,⟨patch_mem6_0_1_5,⟨patch_mem6_0_1_7,⟨patch_mem6_0_1_8,⟨patch_mem6_0_1_10,⟨patch_mem6_0_1_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
