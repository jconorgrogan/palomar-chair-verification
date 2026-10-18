module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock4T0C0
public import SpectreFinite.RadiusFivePruningLiteralBlock4T0C1
public import SpectreFinite.RadiusFivePruningLiteralBlock4T0C2
public import SpectreFinite.RadiusFivePruningLiteralBlock4T0C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq4_0_0_1 : RadiusFivePruning.stateRow4_0_0_1 = ParentOwnership.parentRow0967 := by rfl
theorem patch_mem4_0_0_1 : RadiusFivePruning.patch4_0_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0967, parentRow_mem0967, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0967_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_0_1]
  rfl
theorem row_eq4_0_0_3 : RadiusFivePruning.stateRow4_0_0_3 = ParentOwnership.parentRow0982 := by rfl
theorem patch_mem4_0_0_3 : RadiusFivePruning.patch4_0_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0982, parentRow_mem0982, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0982_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_0_3]
  rfl
theorem row_eq4_0_0_4 : RadiusFivePruning.stateRow4_0_0_4 = ParentOwnership.parentRow0983 := by rfl
theorem patch_mem4_0_0_4 : RadiusFivePruning.patch4_0_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0983, parentRow_mem0983, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0983_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_0_4]
  rfl
theorem row_eq4_0_0_6 : RadiusFivePruning.stateRow4_0_0_6 = ParentOwnership.parentRow0984 := by rfl
theorem patch_mem4_0_0_6 : RadiusFivePruning.patch4_0_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0984, parentRow_mem0984, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0984_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_0_6]
  rfl
theorem row_eq4_0_0_7 : RadiusFivePruning.stateRow4_0_0_7 = ParentOwnership.parentRow0985 := by rfl
theorem patch_mem4_0_0_7 : RadiusFivePruning.patch4_0_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0985, parentRow_mem0985, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0985_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_0_7]
  rfl
theorem row_eq4_0_0_9 : RadiusFivePruning.stateRow4_0_0_9 = ParentOwnership.parentRow0986 := by rfl
theorem patch_mem4_0_0_9 : RadiusFivePruning.patch4_0_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0986, parentRow_mem0986, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0986_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_0_9]
  rfl
theorem row_eq4_0_0_10 : RadiusFivePruning.stateRow4_0_0_10 = ParentOwnership.parentRow0987 := by rfl
theorem patch_mem4_0_0_10 : RadiusFivePruning.patch4_0_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0987, parentRow_mem0987, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0987_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_0_10]
  rfl
theorem row_eq4_0_0_11 : RadiusFivePruning.stateRow4_0_0_11 = ParentOwnership.parentRow0988 := by rfl
theorem patch_mem4_0_0_11 : RadiusFivePruning.patch4_0_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0988, parentRow_mem0988, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0988_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_0_11]
  rfl
theorem chunk_mem4_0_0 : ∀ p ∈ RadiusFivePruning.final4_0_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_0_0, List.forall_mem_cons]
  exact ⟨patch_mem4_0_0_1,⟨patch_mem4_0_0_3,⟨patch_mem4_0_0_4,⟨patch_mem4_0_0_6,⟨patch_mem4_0_0_7,⟨patch_mem4_0_0_9,⟨patch_mem4_0_0_10,⟨patch_mem4_0_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_0_1_0 : RadiusFivePruning.stateRow4_0_1_0 = ParentOwnership.parentRow0989 := by rfl
theorem patch_mem4_0_1_0 : RadiusFivePruning.patch4_0_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0989, parentRow_mem0989, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0989_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_1_0]
  rfl
theorem row_eq4_0_1_1 : RadiusFivePruning.stateRow4_0_1_1 = ParentOwnership.parentRow0990 := by rfl
theorem patch_mem4_0_1_1 : RadiusFivePruning.patch4_0_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0990, parentRow_mem0990, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0990_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_1_1]
  rfl
theorem row_eq4_0_1_3 : RadiusFivePruning.stateRow4_0_1_3 = ParentOwnership.parentRow0991 := by rfl
theorem patch_mem4_0_1_3 : RadiusFivePruning.patch4_0_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0991, parentRow_mem0991, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0991_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_1_3]
  rfl
theorem row_eq4_0_1_4 : RadiusFivePruning.stateRow4_0_1_4 = ParentOwnership.parentRow0992 := by rfl
theorem patch_mem4_0_1_4 : RadiusFivePruning.patch4_0_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0992, parentRow_mem0992, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0992_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_1_4]
  rfl
theorem row_eq4_0_1_5 : RadiusFivePruning.stateRow4_0_1_5 = ParentOwnership.parentRow2041 := by rfl
theorem patch_mem4_0_1_5 : RadiusFivePruning.patch4_0_1_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2041, parentRow_mem2041, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2041_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_1_5]
  rfl
theorem row_eq4_0_1_6 : RadiusFivePruning.stateRow4_0_1_6 = ParentOwnership.parentRow2047 := by rfl
theorem patch_mem4_0_1_6 : RadiusFivePruning.patch4_0_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2047, parentRow_mem2047, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2047_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_1_6]
  rfl
theorem row_eq4_0_1_7 : RadiusFivePruning.stateRow4_0_1_7 = ParentOwnership.parentRow2052 := by rfl
theorem patch_mem4_0_1_7 : RadiusFivePruning.patch4_0_1_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2052, parentRow_mem2052, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2052_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_1_7]
  rfl
theorem row_eq4_0_1_8 : RadiusFivePruning.stateRow4_0_1_8 = ParentOwnership.parentRow2053 := by rfl
theorem patch_mem4_0_1_8 : RadiusFivePruning.patch4_0_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2053, parentRow_mem2053, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2053_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_1_8]
  rfl
theorem row_eq4_0_1_10 : RadiusFivePruning.stateRow4_0_1_10 = ParentOwnership.parentRow2054 := by rfl
theorem patch_mem4_0_1_10 : RadiusFivePruning.patch4_0_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2054, parentRow_mem2054, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2054_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_1_10]
  rfl
theorem chunk_mem4_0_1 : ∀ p ∈ RadiusFivePruning.final4_0_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_0_1, List.forall_mem_cons]
  exact ⟨patch_mem4_0_1_0,⟨patch_mem4_0_1_1,⟨patch_mem4_0_1_3,⟨patch_mem4_0_1_4,⟨patch_mem4_0_1_5,⟨patch_mem4_0_1_6,⟨patch_mem4_0_1_7,⟨patch_mem4_0_1_8,⟨patch_mem4_0_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_0_2_0 : RadiusFivePruning.stateRow4_0_2_0 = ParentOwnership.parentRow0053 := by rfl
theorem patch_mem4_0_2_0 : RadiusFivePruning.patch4_0_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0053, parentRow_mem0053, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0053_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_2_0]
  rfl
theorem row_eq4_0_2_1 : RadiusFivePruning.stateRow4_0_2_1 = ParentOwnership.parentRow0054 := by rfl
theorem patch_mem4_0_2_1 : RadiusFivePruning.patch4_0_2_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0054, parentRow_mem0054, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0054_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_2_1]
  rfl
theorem row_eq4_0_2_2 : RadiusFivePruning.stateRow4_0_2_2 = ParentOwnership.parentRow0056 := by rfl
theorem patch_mem4_0_2_2 : RadiusFivePruning.patch4_0_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0056, parentRow_mem0056, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0056_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_2_2]
  rfl
theorem row_eq4_0_2_4 : RadiusFivePruning.stateRow4_0_2_4 = ParentOwnership.parentRow0500 := by rfl
theorem patch_mem4_0_2_4 : RadiusFivePruning.patch4_0_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0500, parentRow_mem0500, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0500_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_2_4]
  rfl
theorem row_eq4_0_2_6 : RadiusFivePruning.stateRow4_0_2_6 = ParentOwnership.parentRow0975 := by rfl
theorem patch_mem4_0_2_6 : RadiusFivePruning.patch4_0_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0975, parentRow_mem0975, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0975_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_2_6]
  rfl
theorem row_eq4_0_2_7 : RadiusFivePruning.stateRow4_0_2_7 = ParentOwnership.parentRow0976 := by rfl
theorem patch_mem4_0_2_7 : RadiusFivePruning.patch4_0_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0976, parentRow_mem0976, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0976_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_2_7]
  rfl
theorem row_eq4_0_2_9 : RadiusFivePruning.stateRow4_0_2_9 = ParentOwnership.parentRow0977 := by rfl
theorem patch_mem4_0_2_9 : RadiusFivePruning.patch4_0_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0977, parentRow_mem0977, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0977_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_2_9]
  rfl
theorem row_eq4_0_2_10 : RadiusFivePruning.stateRow4_0_2_10 = ParentOwnership.parentRow0978 := by rfl
theorem patch_mem4_0_2_10 : RadiusFivePruning.patch4_0_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0978, parentRow_mem0978, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0978_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_2_10]
  rfl
theorem row_eq4_0_2_11 : RadiusFivePruning.stateRow4_0_2_11 = ParentOwnership.parentRow0979 := by rfl
theorem patch_mem4_0_2_11 : RadiusFivePruning.patch4_0_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0979, parentRow_mem0979, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0979_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_2_11]
  rfl
theorem chunk_mem4_0_2 : ∀ p ∈ RadiusFivePruning.final4_0_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_0_2, List.forall_mem_cons]
  exact ⟨patch_mem4_0_2_0,⟨patch_mem4_0_2_1,⟨patch_mem4_0_2_2,⟨patch_mem4_0_2_4,⟨patch_mem4_0_2_6,⟨patch_mem4_0_2_7,⟨patch_mem4_0_2_9,⟨patch_mem4_0_2_10,⟨patch_mem4_0_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq4_0_3_0 : RadiusFivePruning.stateRow4_0_3_0 = ParentOwnership.parentRow0980 := by rfl
theorem patch_mem4_0_3_0 : RadiusFivePruning.patch4_0_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0980, parentRow_mem0980, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0980_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_3_0]
  rfl
theorem row_eq4_0_3_1 : RadiusFivePruning.stateRow4_0_3_1 = ParentOwnership.parentRow0981 := by rfl
theorem patch_mem4_0_3_1 : RadiusFivePruning.patch4_0_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0981, parentRow_mem0981, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0981_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_3_1]
  rfl
theorem row_eq4_0_3_2 : RadiusFivePruning.stateRow4_0_3_2 = ParentOwnership.parentRow0955 := by rfl
theorem patch_mem4_0_3_2 : RadiusFivePruning.patch4_0_3_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0955, parentRow_mem0955, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0955_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_3_2]
  rfl
theorem row_eq4_0_3_3 : RadiusFivePruning.stateRow4_0_3_3 = ParentOwnership.parentRow0956 := by rfl
theorem patch_mem4_0_3_3 : RadiusFivePruning.patch4_0_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0956, parentRow_mem0956, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0956_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_3_3]
  rfl
theorem row_eq4_0_3_4 : RadiusFivePruning.stateRow4_0_3_4 = ParentOwnership.parentRow0957 := by rfl
theorem patch_mem4_0_3_4 : RadiusFivePruning.patch4_0_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0957, parentRow_mem0957, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0957_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_3_4]
  rfl
theorem row_eq4_0_3_6 : RadiusFivePruning.stateRow4_0_3_6 = ParentOwnership.parentRow0958 := by rfl
theorem patch_mem4_0_3_6 : RadiusFivePruning.patch4_0_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0958, parentRow_mem0958, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0958_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_3_6]
  rfl
theorem row_eq4_0_3_7 : RadiusFivePruning.stateRow4_0_3_7 = ParentOwnership.parentRow0959 := by rfl
theorem patch_mem4_0_3_7 : RadiusFivePruning.patch4_0_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0959, parentRow_mem0959, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0959_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_3_7]
  rfl
theorem row_eq4_0_3_9 : RadiusFivePruning.stateRow4_0_3_9 = ParentOwnership.parentRow0608 := by rfl
theorem patch_mem4_0_3_9 : RadiusFivePruning.patch4_0_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0608, parentRow_mem0608, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0608_property.1, ← literalDomain_eq_hexRegion, ← row_eq4_0_3_9]
  rfl
theorem chunk_mem4_0_3 : ∀ p ∈ RadiusFivePruning.final4_0_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final4_0_3, List.forall_mem_cons]
  exact ⟨patch_mem4_0_3_0,⟨patch_mem4_0_3_1,⟨patch_mem4_0_3_2,⟨patch_mem4_0_3_3,⟨patch_mem4_0_3_4,⟨patch_mem4_0_3_6,⟨patch_mem4_0_3_7,⟨patch_mem4_0_3_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
