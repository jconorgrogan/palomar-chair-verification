module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock4T4C0
public import SpectreFinite.RadiusFivePruningLiteralBlock4T4C1
public import SpectreFinite.RadiusFivePruningLiteralBlock4T4C2
public import SpectreFinite.RadiusFivePruningLiteralBlock4T4C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq4_4_0_1 : RadiusFivePruning.stateRow4_4_0_1 = ParentOwnership.parentRow1876 := by rfl
theorem patch_mem4_4_0_1 : RadiusFivePruning.patch4_4_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1876, parentRow_mem1876, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1876_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_0_1]
  rfl
theorem row_eq4_4_0_3 : RadiusFivePruning.stateRow4_4_0_3 = ParentOwnership.parentRow1875 := by rfl
theorem patch_mem4_4_0_3 : RadiusFivePruning.patch4_4_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1875, parentRow_mem1875, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1875_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_0_3]
  rfl
theorem row_eq4_4_0_4 : RadiusFivePruning.stateRow4_4_0_4 = ParentOwnership.parentRow0876 := by rfl
theorem patch_mem4_4_0_4 : RadiusFivePruning.patch4_4_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0876, parentRow_mem0876, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0876_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_0_4]
  rfl
theorem row_eq4_4_0_6 : RadiusFivePruning.stateRow4_4_0_6 = ParentOwnership.parentRow1877 := by rfl
theorem patch_mem4_4_0_6 : RadiusFivePruning.patch4_4_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1877, parentRow_mem1877, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1877_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_0_6]
  rfl
theorem row_eq4_4_0_7 : RadiusFivePruning.stateRow4_4_0_7 = ParentOwnership.parentRow1889 := by rfl
theorem patch_mem4_4_0_7 : RadiusFivePruning.patch4_4_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1889, parentRow_mem1889, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1889_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_0_7]
  rfl
theorem row_eq4_4_0_9 : RadiusFivePruning.stateRow4_4_0_9 = ParentOwnership.parentRow1878 := by rfl
theorem patch_mem4_4_0_9 : RadiusFivePruning.patch4_4_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1878, parentRow_mem1878, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1878_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_0_9]
  rfl
theorem row_eq4_4_0_10 : RadiusFivePruning.stateRow4_4_0_10 = ParentOwnership.parentRow1890 := by rfl
theorem patch_mem4_4_0_10 : RadiusFivePruning.patch4_4_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1890, parentRow_mem1890, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1890_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_0_10]
  rfl
theorem row_eq4_4_0_11 : RadiusFivePruning.stateRow4_4_0_11 = ParentOwnership.parentRow1405 := by rfl
theorem patch_mem4_4_0_11 : RadiusFivePruning.patch4_4_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1405, parentRow_mem1405, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1405_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_0_11]
  rfl
theorem chunk_mem4_4_0 : ∀ p ∈ RadiusFivePruning.final4_4_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_4_0, List.forall_mem_cons]
  exact ⟨patch_mem4_4_0_1,⟨patch_mem4_4_0_3,⟨patch_mem4_4_0_4,⟨patch_mem4_4_0_6,⟨patch_mem4_4_0_7,⟨patch_mem4_4_0_9,⟨patch_mem4_4_0_10,⟨patch_mem4_4_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_4_1_0 : RadiusFivePruning.stateRow4_4_1_0 = ParentOwnership.parentRow0870 := by rfl
theorem patch_mem4_4_1_0 : RadiusFivePruning.patch4_4_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0870, parentRow_mem0870, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0870_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_1_0]
  rfl
theorem row_eq4_4_1_1 : RadiusFivePruning.stateRow4_4_1_1 = ParentOwnership.parentRow0875 := by rfl
theorem patch_mem4_4_1_1 : RadiusFivePruning.patch4_4_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0875, parentRow_mem0875, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0875_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_1_1]
  rfl
theorem row_eq4_4_1_3 : RadiusFivePruning.stateRow4_4_1_3 = ParentOwnership.parentRow0593 := by rfl
theorem patch_mem4_4_1_3 : RadiusFivePruning.patch4_4_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0593, parentRow_mem0593, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0593_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_1_3]
  rfl
theorem row_eq4_4_1_4 : RadiusFivePruning.stateRow4_4_1_4 = ParentOwnership.parentRow0877 := by rfl
theorem patch_mem4_4_1_4 : RadiusFivePruning.patch4_4_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0877, parentRow_mem0877, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0877_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_1_4]
  rfl
theorem row_eq4_4_1_5 : RadiusFivePruning.stateRow4_4_1_5 = ParentOwnership.parentRow1873 := by rfl
theorem patch_mem4_4_1_5 : RadiusFivePruning.patch4_4_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1873, parentRow_mem1873, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1873_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_1_5]
  rfl
theorem row_eq4_4_1_6 : RadiusFivePruning.stateRow4_4_1_6 = ParentOwnership.parentRow1887 := by rfl
theorem patch_mem4_4_1_6 : RadiusFivePruning.patch4_4_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1887, parentRow_mem1887, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1887_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_1_6]
  rfl
theorem row_eq4_4_1_7 : RadiusFivePruning.stateRow4_4_1_7 = ParentOwnership.parentRow1874 := by rfl
theorem patch_mem4_4_1_7 : RadiusFivePruning.patch4_4_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1874, parentRow_mem1874, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1874_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_1_7]
  rfl
theorem row_eq4_4_1_8 : RadiusFivePruning.stateRow4_4_1_8 = ParentOwnership.parentRow1886 := by rfl
theorem patch_mem4_4_1_8 : RadiusFivePruning.patch4_4_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1886, parentRow_mem1886, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1886_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_1_8]
  rfl
theorem row_eq4_4_1_10 : RadiusFivePruning.stateRow4_4_1_10 = ParentOwnership.parentRow1888 := by rfl
theorem patch_mem4_4_1_10 : RadiusFivePruning.patch4_4_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1888, parentRow_mem1888, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1888_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_1_10]
  rfl
theorem chunk_mem4_4_1 : ∀ p ∈ RadiusFivePruning.final4_4_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_4_1, List.forall_mem_cons]
  exact ⟨patch_mem4_4_1_0,⟨patch_mem4_4_1_1,⟨patch_mem4_4_1_3,⟨patch_mem4_4_1_4,⟨patch_mem4_4_1_5,⟨patch_mem4_4_1_6,⟨patch_mem4_4_1_7,⟨patch_mem4_4_1_8,⟨patch_mem4_4_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_4_2_0 : RadiusFivePruning.stateRow4_4_2_0 = ParentOwnership.parentRow1438 := by rfl
theorem patch_mem4_4_2_0 : RadiusFivePruning.patch4_4_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1438, parentRow_mem1438, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1438_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_2_0]
  rfl
theorem row_eq4_4_2_1 : RadiusFivePruning.stateRow4_4_2_1 = ParentOwnership.parentRow1444 := by rfl
theorem patch_mem4_4_2_1 : RadiusFivePruning.patch4_4_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1444, parentRow_mem1444, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1444_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_2_1]
  rfl
theorem row_eq4_4_2_2 : RadiusFivePruning.stateRow4_4_2_2 = ParentOwnership.parentRow1437 := by rfl
theorem patch_mem4_4_2_2 : RadiusFivePruning.patch4_4_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1437, parentRow_mem1437, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1437_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_2_2]
  rfl
theorem row_eq4_4_2_4 : RadiusFivePruning.stateRow4_4_2_4 = ParentOwnership.parentRow1443 := by rfl
theorem patch_mem4_4_2_4 : RadiusFivePruning.patch4_4_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1443, parentRow_mem1443, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1443_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_2_4]
  rfl
theorem row_eq4_4_2_6 : RadiusFivePruning.stateRow4_4_2_6 = ParentOwnership.parentRow1828 := by rfl
theorem patch_mem4_4_2_6 : RadiusFivePruning.patch4_4_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1828, parentRow_mem1828, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1828_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_2_6]
  rfl
theorem row_eq4_4_2_7 : RadiusFivePruning.stateRow4_4_2_7 = ParentOwnership.parentRow1829 := by rfl
theorem patch_mem4_4_2_7 : RadiusFivePruning.patch4_4_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1829, parentRow_mem1829, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1829_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_2_7]
  rfl
theorem row_eq4_4_2_9 : RadiusFivePruning.stateRow4_4_2_9 = ParentOwnership.parentRow1398 := by rfl
theorem patch_mem4_4_2_9 : RadiusFivePruning.patch4_4_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1398, parentRow_mem1398, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1398_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_2_9]
  rfl
theorem row_eq4_4_2_10 : RadiusFivePruning.stateRow4_4_2_10 = ParentOwnership.parentRow1830 := by rfl
theorem patch_mem4_4_2_10 : RadiusFivePruning.patch4_4_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1830, parentRow_mem1830, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1830_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_2_10]
  rfl
theorem row_eq4_4_2_11 : RadiusFivePruning.stateRow4_4_2_11 = ParentOwnership.parentRow1385 := by rfl
theorem patch_mem4_4_2_11 : RadiusFivePruning.patch4_4_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1385, parentRow_mem1385, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1385_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_2_11]
  rfl
theorem chunk_mem4_4_2 : ∀ p ∈ RadiusFivePruning.final4_4_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_4_2, List.forall_mem_cons]
  exact ⟨patch_mem4_4_2_0,⟨patch_mem4_4_2_1,⟨patch_mem4_4_2_2,⟨patch_mem4_4_2_4,⟨patch_mem4_4_2_6,⟨patch_mem4_4_2_7,⟨patch_mem4_4_2_9,⟨patch_mem4_4_2_10,⟨patch_mem4_4_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_4_3_0 : RadiusFivePruning.stateRow4_4_3_0 = ParentOwnership.parentRow1831 := by rfl
theorem patch_mem4_4_3_0 : RadiusFivePruning.patch4_4_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1831, parentRow_mem1831, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1831_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_3_0]
  rfl
theorem row_eq4_4_3_1 : RadiusFivePruning.stateRow4_4_3_1 = ParentOwnership.parentRow1386 := by rfl
theorem patch_mem4_4_3_1 : RadiusFivePruning.patch4_4_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1386, parentRow_mem1386, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1386_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_3_1]
  rfl
theorem row_eq4_4_3_2 : RadiusFivePruning.stateRow4_4_3_2 = ParentOwnership.parentRow1406 := by rfl
theorem patch_mem4_4_3_2 : RadiusFivePruning.patch4_4_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1406, parentRow_mem1406, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1406_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_3_2]
  rfl
theorem row_eq4_4_3_3 : RadiusFivePruning.stateRow4_4_3_3 = ParentOwnership.parentRow1832 := by rfl
theorem patch_mem4_4_3_3 : RadiusFivePruning.patch4_4_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1832, parentRow_mem1832, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1832_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_3_3]
  rfl
theorem row_eq4_4_3_4 : RadiusFivePruning.stateRow4_4_3_4 = ParentOwnership.parentRow1833 := by rfl
theorem patch_mem4_4_3_4 : RadiusFivePruning.patch4_4_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1833, parentRow_mem1833, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1833_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_3_4]
  rfl
theorem row_eq4_4_3_6 : RadiusFivePruning.stateRow4_4_3_6 = ParentOwnership.parentRow1834 := by rfl
theorem patch_mem4_4_3_6 : RadiusFivePruning.patch4_4_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1834, parentRow_mem1834, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1834_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_3_6]
  rfl
theorem row_eq4_4_3_7 : RadiusFivePruning.stateRow4_4_3_7 = ParentOwnership.parentRow1390 := by rfl
theorem patch_mem4_4_3_7 : RadiusFivePruning.patch4_4_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1390, parentRow_mem1390, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1390_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_3_7]
  rfl
theorem row_eq4_4_3_9 : RadiusFivePruning.stateRow4_4_3_9 = ParentOwnership.parentRow1428 := by rfl
theorem patch_mem4_4_3_9 : RadiusFivePruning.patch4_4_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1428, parentRow_mem1428, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1428_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_4_3_9]
  rfl
theorem chunk_mem4_4_3 : ∀ p ∈ RadiusFivePruning.final4_4_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_4_3, List.forall_mem_cons]
  exact ⟨patch_mem4_4_3_0,⟨patch_mem4_4_3_1,⟨patch_mem4_4_3_2,⟨patch_mem4_4_3_3,⟨patch_mem4_4_3_4,⟨patch_mem4_4_3_6,⟨patch_mem4_4_3_7,⟨patch_mem4_4_3_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
