module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock8T4C0
public import SpectreFinite.RadiusFivePruningLiteralBlock8T4C1
public import SpectreFinite.RadiusFivePruningLiteralBlock8T4C2
public import SpectreFinite.RadiusFivePruningLiteralBlock8T4C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq8_4_0_1 : RadiusFivePruning.stateRow8_4_0_1 = ParentOwnership.parentRow1879 := by rfl
theorem patch_mem8_4_0_1 : RadiusFivePruning.patch8_4_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1879, parentRow_mem1879, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1879_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_0_1]
  rfl
theorem row_eq8_4_0_3 : RadiusFivePruning.stateRow8_4_0_3 = ParentOwnership.parentRow1865 := by rfl
theorem patch_mem8_4_0_3 : RadiusFivePruning.patch8_4_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1865, parentRow_mem1865, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1865_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_0_3]
  rfl
theorem row_eq8_4_0_4 : RadiusFivePruning.stateRow8_4_0_4 = ParentOwnership.parentRow1880 := by rfl
theorem patch_mem8_4_0_4 : RadiusFivePruning.patch8_4_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1880, parentRow_mem1880, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1880_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_0_4]
  rfl
theorem row_eq8_4_0_5 : RadiusFivePruning.stateRow8_4_0_5 = ParentOwnership.parentRow0661 := by rfl
theorem patch_mem8_4_0_5 : RadiusFivePruning.patch8_4_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0661, parentRow_mem0661, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0661_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_0_5]
  rfl
theorem row_eq8_4_0_6 : RadiusFivePruning.stateRow8_4_0_6 = ParentOwnership.parentRow0677 := by rfl
theorem patch_mem8_4_0_6 : RadiusFivePruning.patch8_4_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0677, parentRow_mem0677, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0677_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_0_6]
  rfl
theorem row_eq8_4_0_7 : RadiusFivePruning.stateRow8_4_0_7 = ParentOwnership.parentRow1881 := by rfl
theorem patch_mem8_4_0_7 : RadiusFivePruning.patch8_4_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1881, parentRow_mem1881, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1881_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_0_7]
  rfl
theorem row_eq8_4_0_8 : RadiusFivePruning.stateRow8_4_0_8 = ParentOwnership.parentRow1882 := by rfl
theorem patch_mem8_4_0_8 : RadiusFivePruning.patch8_4_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1882, parentRow_mem1882, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1882_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_0_8]
  rfl
theorem row_eq8_4_0_9 : RadiusFivePruning.stateRow8_4_0_9 = ParentOwnership.parentRow1870 := by rfl
theorem patch_mem8_4_0_9 : RadiusFivePruning.patch8_4_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1870, parentRow_mem1870, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1870_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_0_9]
  rfl
theorem row_eq8_4_0_10 : RadiusFivePruning.stateRow8_4_0_10 = ParentOwnership.parentRow0662 := by rfl
theorem patch_mem8_4_0_10 : RadiusFivePruning.patch8_4_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0662, parentRow_mem0662, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0662_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_0_10]
  rfl
theorem row_eq8_4_0_11 : RadiusFivePruning.stateRow8_4_0_11 = ParentOwnership.parentRow0659 := by rfl
theorem patch_mem8_4_0_11 : RadiusFivePruning.patch8_4_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0659, parentRow_mem0659, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0659_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_0_11]
  rfl
theorem chunk_mem8_4_0 : ∀ p ∈ RadiusFivePruning.final8_4_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_4_0, List.forall_mem_cons]
  exact ⟨patch_mem8_4_0_1,⟨patch_mem8_4_0_3,⟨patch_mem8_4_0_4,⟨patch_mem8_4_0_5,⟨patch_mem8_4_0_6,⟨patch_mem8_4_0_7,⟨patch_mem8_4_0_8,⟨patch_mem8_4_0_9,⟨patch_mem8_4_0_10,⟨patch_mem8_4_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_4_1_0 : RadiusFivePruning.stateRow8_4_1_0 = ParentOwnership.parentRow0660 := by rfl
theorem patch_mem8_4_1_0 : RadiusFivePruning.patch8_4_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0660, parentRow_mem0660, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0660_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_1_0]
  rfl
theorem row_eq8_4_1_1 : RadiusFivePruning.stateRow8_4_1_1 = ParentOwnership.parentRow1825 := by rfl
theorem patch_mem8_4_1_1 : RadiusFivePruning.patch8_4_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1825, parentRow_mem1825, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1825_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_1_1]
  rfl
theorem row_eq8_4_1_2 : RadiusFivePruning.stateRow8_4_1_2 = ParentOwnership.parentRow0678 := by rfl
theorem patch_mem8_4_1_2 : RadiusFivePruning.patch8_4_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0678, parentRow_mem0678, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0678_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_1_2]
  rfl
theorem row_eq8_4_1_3 : RadiusFivePruning.stateRow8_4_1_3 = ParentOwnership.parentRow0670 := by rfl
theorem patch_mem8_4_1_3 : RadiusFivePruning.patch8_4_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0670, parentRow_mem0670, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0670_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_1_3]
  rfl
theorem row_eq8_4_1_4 : RadiusFivePruning.stateRow8_4_1_4 = ParentOwnership.parentRow0676 := by rfl
theorem patch_mem8_4_1_4 : RadiusFivePruning.patch8_4_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0676, parentRow_mem0676, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0676_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_1_4]
  rfl
theorem row_eq8_4_1_6 : RadiusFivePruning.stateRow8_4_1_6 = ParentOwnership.parentRow1872 := by rfl
theorem patch_mem8_4_1_6 : RadiusFivePruning.patch8_4_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1872, parentRow_mem1872, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1872_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_1_6]
  rfl
theorem row_eq8_4_1_8 : RadiusFivePruning.stateRow8_4_1_8 = ParentOwnership.parentRow1883 := by rfl
theorem patch_mem8_4_1_8 : RadiusFivePruning.patch8_4_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1883, parentRow_mem1883, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1883_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_1_8]
  rfl
theorem row_eq8_4_1_9 : RadiusFivePruning.stateRow8_4_1_9 = ParentOwnership.parentRow1866 := by rfl
theorem patch_mem8_4_1_9 : RadiusFivePruning.patch8_4_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1866, parentRow_mem1866, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1866_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_1_9]
  rfl
theorem row_eq8_4_1_10 : RadiusFivePruning.stateRow8_4_1_10 = ParentOwnership.parentRow1867 := by rfl
theorem patch_mem8_4_1_10 : RadiusFivePruning.patch8_4_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1867, parentRow_mem1867, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1867_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_1_10]
  rfl
theorem chunk_mem8_4_1 : ∀ p ∈ RadiusFivePruning.final8_4_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_4_1, List.forall_mem_cons]
  exact ⟨patch_mem8_4_1_0,⟨patch_mem8_4_1_1,⟨patch_mem8_4_1_2,⟨patch_mem8_4_1_3,⟨patch_mem8_4_1_4,⟨patch_mem8_4_1_6,⟨patch_mem8_4_1_8,⟨patch_mem8_4_1_9,⟨patch_mem8_4_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_4_2_0 : RadiusFivePruning.stateRow8_4_2_0 = ParentOwnership.parentRow1871 := by rfl
theorem patch_mem8_4_2_0 : RadiusFivePruning.patch8_4_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1871, parentRow_mem1871, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1871_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_2_0]
  rfl
theorem row_eq8_4_2_2 : RadiusFivePruning.stateRow8_4_2_2 = ParentOwnership.parentRow1884 := by rfl
theorem patch_mem8_4_2_2 : RadiusFivePruning.patch8_4_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1884, parentRow_mem1884, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1884_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_2_2]
  rfl
theorem row_eq8_4_2_3 : RadiusFivePruning.stateRow8_4_2_3 = ParentOwnership.parentRow1885 := by rfl
theorem patch_mem8_4_2_3 : RadiusFivePruning.patch8_4_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1885, parentRow_mem1885, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1885_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_2_3]
  rfl
theorem row_eq8_4_2_4 : RadiusFivePruning.stateRow8_4_2_4 = ParentOwnership.parentRow1868 := by rfl
theorem patch_mem8_4_2_4 : RadiusFivePruning.patch8_4_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1868, parentRow_mem1868, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1868_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_2_4]
  rfl
theorem row_eq8_4_2_5 : RadiusFivePruning.stateRow8_4_2_5 = ParentOwnership.parentRow1869 := by rfl
theorem patch_mem8_4_2_5 : RadiusFivePruning.patch8_4_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1869, parentRow_mem1869, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1869_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_2_5]
  rfl
theorem row_eq8_4_2_6 : RadiusFivePruning.stateRow8_4_2_6 = ParentOwnership.parentRow1419 := by rfl
theorem patch_mem8_4_2_6 : RadiusFivePruning.patch8_4_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1419, parentRow_mem1419, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1419_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_2_6]
  rfl
theorem row_eq8_4_2_7 : RadiusFivePruning.stateRow8_4_2_7 = ParentOwnership.parentRow1418 := by rfl
theorem patch_mem8_4_2_7 : RadiusFivePruning.patch8_4_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1418, parentRow_mem1418, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1418_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_2_7]
  rfl
theorem row_eq8_4_2_8 : RadiusFivePruning.stateRow8_4_2_8 = ParentOwnership.parentRow1426 := by rfl
theorem patch_mem8_4_2_8 : RadiusFivePruning.patch8_4_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1426, parentRow_mem1426, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1426_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_2_8]
  rfl
theorem row_eq8_4_2_9 : RadiusFivePruning.stateRow8_4_2_9 = ParentOwnership.parentRow1396 := by rfl
theorem patch_mem8_4_2_9 : RadiusFivePruning.patch8_4_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1396, parentRow_mem1396, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1396_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_2_9]
  rfl
theorem row_eq8_4_2_10 : RadiusFivePruning.stateRow8_4_2_10 = ParentOwnership.parentRow1425 := by rfl
theorem patch_mem8_4_2_10 : RadiusFivePruning.patch8_4_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1425, parentRow_mem1425, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1425_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_2_10]
  rfl
theorem row_eq8_4_2_11 : RadiusFivePruning.stateRow8_4_2_11 = ParentOwnership.parentRow1395 := by rfl
theorem patch_mem8_4_2_11 : RadiusFivePruning.patch8_4_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1395, parentRow_mem1395, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1395_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_2_11]
  rfl
theorem chunk_mem8_4_2 : ∀ p ∈ RadiusFivePruning.final8_4_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_4_2, List.forall_mem_cons]
  exact ⟨patch_mem8_4_2_0,⟨patch_mem8_4_2_2,⟨patch_mem8_4_2_3,⟨patch_mem8_4_2_4,⟨patch_mem8_4_2_5,⟨patch_mem8_4_2_6,⟨patch_mem8_4_2_7,⟨patch_mem8_4_2_8,⟨patch_mem8_4_2_9,⟨patch_mem8_4_2_10,⟨patch_mem8_4_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_4_3_0 : RadiusFivePruning.stateRow8_4_3_0 = ParentOwnership.parentRow0672 := by rfl
theorem patch_mem8_4_3_0 : RadiusFivePruning.patch8_4_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0672, parentRow_mem0672, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0672_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_3_0]
  rfl
theorem row_eq8_4_3_1 : RadiusFivePruning.stateRow8_4_3_1 = ParentOwnership.parentRow0680 := by rfl
theorem patch_mem8_4_3_1 : RadiusFivePruning.patch8_4_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0680, parentRow_mem0680, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0680_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_3_1]
  rfl
theorem row_eq8_4_3_3 : RadiusFivePruning.stateRow8_4_3_3 = ParentOwnership.parentRow0671 := by rfl
theorem patch_mem8_4_3_3 : RadiusFivePruning.patch8_4_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0671, parentRow_mem0671, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0671_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_3_3]
  rfl
theorem row_eq8_4_3_4 : RadiusFivePruning.stateRow8_4_3_4 = ParentOwnership.parentRow0679 := by rfl
theorem patch_mem8_4_3_4 : RadiusFivePruning.patch8_4_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0679, parentRow_mem0679, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0679_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_3_4]
  rfl
theorem row_eq8_4_3_5 : RadiusFivePruning.stateRow8_4_3_5 = ParentOwnership.parentRow1837 := by rfl
theorem patch_mem8_4_3_5 : RadiusFivePruning.patch8_4_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1837, parentRow_mem1837, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1837_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_3_5]
  rfl
theorem row_eq8_4_3_6 : RadiusFivePruning.stateRow8_4_3_6 = ParentOwnership.parentRow1838 := by rfl
theorem patch_mem8_4_3_6 : RadiusFivePruning.patch8_4_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1838, parentRow_mem1838, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1838_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_3_6]
  rfl
theorem row_eq8_4_3_7 : RadiusFivePruning.stateRow8_4_3_7 = ParentOwnership.parentRow1407 := by rfl
theorem patch_mem8_4_3_7 : RadiusFivePruning.patch8_4_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1407, parentRow_mem1407, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1407_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_3_7]
  rfl
theorem row_eq8_4_3_8 : RadiusFivePruning.stateRow8_4_3_8 = ParentOwnership.parentRow1384 := by rfl
theorem patch_mem8_4_3_8 : RadiusFivePruning.patch8_4_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1384, parentRow_mem1384, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1384_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_3_8]
  rfl
theorem row_eq8_4_3_9 : RadiusFivePruning.stateRow8_4_3_9 = ParentOwnership.parentRow1826 := by rfl
theorem patch_mem8_4_3_9 : RadiusFivePruning.patch8_4_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1826, parentRow_mem1826, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1826_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_3_9]
  rfl
theorem row_eq8_4_3_10 : RadiusFivePruning.stateRow8_4_3_10 = ParentOwnership.parentRow1835 := by rfl
theorem patch_mem8_4_3_10 : RadiusFivePruning.patch8_4_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1835, parentRow_mem1835, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1835_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_3_10]
  rfl
theorem row_eq8_4_3_11 : RadiusFivePruning.stateRow8_4_3_11 = ParentOwnership.parentRow1827 := by rfl
theorem patch_mem8_4_3_11 : RadiusFivePruning.patch8_4_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1827, parentRow_mem1827, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1827_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_4_3_11]
  rfl
theorem chunk_mem8_4_3 : ∀ p ∈ RadiusFivePruning.final8_4_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_4_3, List.forall_mem_cons]
  exact ⟨patch_mem8_4_3_0,⟨patch_mem8_4_3_1,⟨patch_mem8_4_3_3,⟨patch_mem8_4_3_4,⟨patch_mem8_4_3_5,⟨patch_mem8_4_3_6,⟨patch_mem8_4_3_7,⟨patch_mem8_4_3_8,⟨patch_mem8_4_3_9,⟨patch_mem8_4_3_10,⟨patch_mem8_4_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
