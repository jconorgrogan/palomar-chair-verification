module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock8T1C2
public import SpectreFinite.RadiusFivePruningLiteralBlock8T1C3
public import SpectreFinite.RadiusFivePruningLiteralBlock8T1C4
public import SpectreFinite.RadiusFivePruningLiteralBlock8T1C5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq8_1_2_0 : RadiusFivePruning.stateRow8_1_2_0 = ParentOwnership.parentRow1961 := by rfl
theorem patch_mem8_1_2_0 : RadiusFivePruning.patch8_1_2_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1961, parentRow_mem1961, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1961_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_2_0]
  rfl
theorem row_eq8_1_2_2 : RadiusFivePruning.stateRow8_1_2_2 = ParentOwnership.parentRow1563 := by rfl
theorem patch_mem8_1_2_2 : RadiusFivePruning.patch8_1_2_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1563, parentRow_mem1563, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1563_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_2_2]
  rfl
theorem row_eq8_1_2_3 : RadiusFivePruning.stateRow8_1_2_3 = ParentOwnership.parentRow1566 := by rfl
theorem patch_mem8_1_2_3 : RadiusFivePruning.patch8_1_2_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1566, parentRow_mem1566, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1566_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_2_3]
  rfl
theorem row_eq8_1_2_4 : RadiusFivePruning.stateRow8_1_2_4 = ParentOwnership.parentRow1564 := by rfl
theorem patch_mem8_1_2_4 : RadiusFivePruning.patch8_1_2_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1564, parentRow_mem1564, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1564_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_2_4]
  rfl
theorem row_eq8_1_2_5 : RadiusFivePruning.stateRow8_1_2_5 = ParentOwnership.parentRow1567 := by rfl
theorem patch_mem8_1_2_5 : RadiusFivePruning.patch8_1_2_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1567, parentRow_mem1567, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1567_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_2_5]
  rfl
theorem row_eq8_1_2_6 : RadiusFivePruning.stateRow8_1_2_6 = ParentOwnership.parentRow0808 := by rfl
theorem patch_mem8_1_2_6 : RadiusFivePruning.patch8_1_2_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0808, parentRow_mem0808, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0808_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_2_6]
  rfl
theorem row_eq8_1_2_7 : RadiusFivePruning.stateRow8_1_2_7 = ParentOwnership.parentRow0817 := by rfl
theorem patch_mem8_1_2_7 : RadiusFivePruning.patch8_1_2_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0817, parentRow_mem0817, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0817_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_2_7]
  rfl
theorem row_eq8_1_2_8 : RadiusFivePruning.stateRow8_1_2_8 = ParentOwnership.parentRow0805 := by rfl
theorem patch_mem8_1_2_8 : RadiusFivePruning.patch8_1_2_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0805, parentRow_mem0805, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0805_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_2_8]
  rfl
theorem row_eq8_1_2_9 : RadiusFivePruning.stateRow8_1_2_9 = ParentOwnership.parentRow0806 := by rfl
theorem patch_mem8_1_2_9 : RadiusFivePruning.patch8_1_2_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0806, parentRow_mem0806, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0806_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_2_9]
  rfl
theorem row_eq8_1_2_10 : RadiusFivePruning.stateRow8_1_2_10 = ParentOwnership.parentRow0812 := by rfl
theorem patch_mem8_1_2_10 : RadiusFivePruning.patch8_1_2_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0812, parentRow_mem0812, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0812_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_2_10]
  rfl
theorem row_eq8_1_2_11 : RadiusFivePruning.stateRow8_1_2_11 = ParentOwnership.parentRow0813 := by rfl
theorem patch_mem8_1_2_11 : RadiusFivePruning.patch8_1_2_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0813, parentRow_mem0813, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0813_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_2_11]
  rfl
theorem chunk_mem8_1_2 : ∀ p ∈ RadiusFivePruning.final8_1_2, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_1_2, List.forall_mem_cons]
  exact ⟨patch_mem8_1_2_0,⟨patch_mem8_1_2_2,⟨patch_mem8_1_2_3,⟨patch_mem8_1_2_4,⟨patch_mem8_1_2_5,⟨patch_mem8_1_2_6,⟨patch_mem8_1_2_7,⟨patch_mem8_1_2_8,⟨patch_mem8_1_2_9,⟨patch_mem8_1_2_10,⟨patch_mem8_1_2_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_1_3_0 : RadiusFivePruning.stateRow8_1_3_0 = ParentOwnership.parentRow0731 := by rfl
theorem patch_mem8_1_3_0 : RadiusFivePruning.patch8_1_3_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0731, parentRow_mem0731, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0731_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_3_0]
  rfl
theorem row_eq8_1_3_1 : RadiusFivePruning.stateRow8_1_3_1 = ParentOwnership.parentRow0732 := by rfl
theorem patch_mem8_1_3_1 : RadiusFivePruning.patch8_1_3_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0732, parentRow_mem0732, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0732_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_3_1]
  rfl
theorem row_eq8_1_3_3 : RadiusFivePruning.stateRow8_1_3_3 = ParentOwnership.parentRow1949 := by rfl
theorem patch_mem8_1_3_3 : RadiusFivePruning.patch8_1_3_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1949, parentRow_mem1949, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1949_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_3_3]
  rfl
theorem row_eq8_1_3_4 : RadiusFivePruning.stateRow8_1_3_4 = ParentOwnership.parentRow1950 := by rfl
theorem patch_mem8_1_3_4 : RadiusFivePruning.patch8_1_3_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1950, parentRow_mem1950, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1950_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_3_4]
  rfl
theorem row_eq8_1_3_5 : RadiusFivePruning.stateRow8_1_3_5 = ParentOwnership.parentRow1951 := by rfl
theorem patch_mem8_1_3_5 : RadiusFivePruning.patch8_1_3_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1951, parentRow_mem1951, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1951_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_3_5]
  rfl
theorem row_eq8_1_3_6 : RadiusFivePruning.stateRow8_1_3_6 = ParentOwnership.parentRow1957 := by rfl
theorem patch_mem8_1_3_6 : RadiusFivePruning.patch8_1_3_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1957, parentRow_mem1957, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1957_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_3_6]
  rfl
theorem row_eq8_1_3_7 : RadiusFivePruning.stateRow8_1_3_7 = ParentOwnership.parentRow1527 := by rfl
theorem patch_mem8_1_3_7 : RadiusFivePruning.patch8_1_3_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1527, parentRow_mem1527, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1527_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_3_7]
  rfl
theorem row_eq8_1_3_8 : RadiusFivePruning.stateRow8_1_3_8 = ParentOwnership.parentRow1529 := by rfl
theorem patch_mem8_1_3_8 : RadiusFivePruning.patch8_1_3_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1529, parentRow_mem1529, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1529_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_3_8]
  rfl
theorem row_eq8_1_3_9 : RadiusFivePruning.stateRow8_1_3_9 = ParentOwnership.parentRow1554 := by rfl
theorem patch_mem8_1_3_9 : RadiusFivePruning.patch8_1_3_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1554, parentRow_mem1554, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1554_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_3_9]
  rfl
theorem row_eq8_1_3_10 : RadiusFivePruning.stateRow8_1_3_10 = ParentOwnership.parentRow1556 := by rfl
theorem patch_mem8_1_3_10 : RadiusFivePruning.patch8_1_3_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1556, parentRow_mem1556, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1556_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_3_10]
  rfl
theorem row_eq8_1_3_11 : RadiusFivePruning.stateRow8_1_3_11 = ParentOwnership.parentRow1573 := by rfl
theorem patch_mem8_1_3_11 : RadiusFivePruning.patch8_1_3_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1573, parentRow_mem1573, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1573_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_3_11]
  rfl
theorem chunk_mem8_1_3 : ∀ p ∈ RadiusFivePruning.final8_1_3, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_1_3, List.forall_mem_cons]
  exact ⟨patch_mem8_1_3_0,⟨patch_mem8_1_3_1,⟨patch_mem8_1_3_3,⟨patch_mem8_1_3_4,⟨patch_mem8_1_3_5,⟨patch_mem8_1_3_6,⟨patch_mem8_1_3_7,⟨patch_mem8_1_3_8,⟨patch_mem8_1_3_9,⟨patch_mem8_1_3_10,⟨patch_mem8_1_3_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_1_4_0 : RadiusFivePruning.stateRow8_1_4_0 = ParentOwnership.parentRow1575 := by rfl
theorem patch_mem8_1_4_0 : RadiusFivePruning.patch8_1_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1575, parentRow_mem1575, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1575_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_4_0]
  rfl
theorem row_eq8_1_4_1 : RadiusFivePruning.stateRow8_1_4_1 = ParentOwnership.parentRow0734 := by rfl
theorem patch_mem8_1_4_1 : RadiusFivePruning.patch8_1_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0734, parentRow_mem0734, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0734_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_4_1]
  rfl
theorem row_eq8_1_4_2 : RadiusFivePruning.stateRow8_1_4_2 = ParentOwnership.parentRow0735 := by rfl
theorem patch_mem8_1_4_2 : RadiusFivePruning.patch8_1_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0735, parentRow_mem0735, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0735_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_4_2]
  rfl
theorem row_eq8_1_4_3 : RadiusFivePruning.stateRow8_1_4_3 = ParentOwnership.parentRow0736 := by rfl
theorem patch_mem8_1_4_3 : RadiusFivePruning.patch8_1_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0736, parentRow_mem0736, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0736_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_4_3]
  rfl
theorem row_eq8_1_4_4 : RadiusFivePruning.stateRow8_1_4_4 = ParentOwnership.parentRow0737 := by rfl
theorem patch_mem8_1_4_4 : RadiusFivePruning.patch8_1_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0737, parentRow_mem0737, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0737_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_4_4]
  rfl
theorem row_eq8_1_4_5 : RadiusFivePruning.stateRow8_1_4_5 = ParentOwnership.parentRow0733 := by rfl
theorem patch_mem8_1_4_5 : RadiusFivePruning.patch8_1_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0733, parentRow_mem0733, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0733_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_4_5]
  rfl
theorem row_eq8_1_4_8 : RadiusFivePruning.stateRow8_1_4_8 = ParentOwnership.parentRow0730 := by rfl
theorem patch_mem8_1_4_8 : RadiusFivePruning.patch8_1_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0730, parentRow_mem0730, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0730_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_4_8]
  rfl
theorem row_eq8_1_4_9 : RadiusFivePruning.stateRow8_1_4_9 = ParentOwnership.parentRow1952 := by rfl
theorem patch_mem8_1_4_9 : RadiusFivePruning.patch8_1_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1952, parentRow_mem1952, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1952_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_4_9]
  rfl
theorem row_eq8_1_4_10 : RadiusFivePruning.stateRow8_1_4_10 = ParentOwnership.parentRow1953 := by rfl
theorem patch_mem8_1_4_10 : RadiusFivePruning.patch8_1_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1953, parentRow_mem1953, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1953_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_4_10]
  rfl
theorem row_eq8_1_4_11 : RadiusFivePruning.stateRow8_1_4_11 = ParentOwnership.parentRow1958 := by rfl
theorem patch_mem8_1_4_11 : RadiusFivePruning.patch8_1_4_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1958, parentRow_mem1958, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1958_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_4_11]
  rfl
theorem chunk_mem8_1_4 : ∀ p ∈ RadiusFivePruning.final8_1_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_1_4, List.forall_mem_cons]
  exact ⟨patch_mem8_1_4_0,⟨patch_mem8_1_4_1,⟨patch_mem8_1_4_2,⟨patch_mem8_1_4_3,⟨patch_mem8_1_4_4,⟨patch_mem8_1_4_5,⟨patch_mem8_1_4_8,⟨patch_mem8_1_4_9,⟨patch_mem8_1_4_10,⟨patch_mem8_1_4_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_1_5_0 : RadiusFivePruning.stateRow8_1_5_0 = ParentOwnership.parentRow1959 := by rfl
theorem patch_mem8_1_5_0 : RadiusFivePruning.patch8_1_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1959, parentRow_mem1959, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1959_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_5_0]
  rfl
theorem row_eq8_1_5_1 : RadiusFivePruning.stateRow8_1_5_1 = ParentOwnership.parentRow1954 := by rfl
theorem patch_mem8_1_5_1 : RadiusFivePruning.patch8_1_5_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1954, parentRow_mem1954, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1954_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_5_1]
  rfl
theorem row_eq8_1_5_2 : RadiusFivePruning.stateRow8_1_5_2 = ParentOwnership.parentRow1955 := by rfl
theorem patch_mem8_1_5_2 : RadiusFivePruning.patch8_1_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1955, parentRow_mem1955, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1955_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_5_2]
  rfl
theorem row_eq8_1_5_3 : RadiusFivePruning.stateRow8_1_5_3 = ParentOwnership.parentRow1960 := by rfl
theorem patch_mem8_1_5_3 : RadiusFivePruning.patch8_1_5_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1960, parentRow_mem1960, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1960_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_5_3]
  rfl
theorem row_eq8_1_5_4 : RadiusFivePruning.stateRow8_1_5_4 = ParentOwnership.parentRow1528 := by rfl
theorem patch_mem8_1_5_4 : RadiusFivePruning.patch8_1_5_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1528, parentRow_mem1528, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1528_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_5_4]
  rfl
theorem row_eq8_1_5_5 : RadiusFivePruning.stateRow8_1_5_5 = ParentOwnership.parentRow1530 := by rfl
theorem patch_mem8_1_5_5 : RadiusFivePruning.patch8_1_5_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1530, parentRow_mem1530, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1530_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_5_5]
  rfl
theorem row_eq8_1_5_6 : RadiusFivePruning.stateRow8_1_5_6 = ParentOwnership.parentRow1555 := by rfl
theorem patch_mem8_1_5_6 : RadiusFivePruning.patch8_1_5_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1555, parentRow_mem1555, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1555_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_5_6]
  rfl
theorem row_eq8_1_5_7 : RadiusFivePruning.stateRow8_1_5_7 = ParentOwnership.parentRow1557 := by rfl
theorem patch_mem8_1_5_7 : RadiusFivePruning.patch8_1_5_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1557, parentRow_mem1557, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1557_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_5_7]
  rfl
theorem row_eq8_1_5_8 : RadiusFivePruning.stateRow8_1_5_8 = ParentOwnership.parentRow1574 := by rfl
theorem patch_mem8_1_5_8 : RadiusFivePruning.patch8_1_5_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1574, parentRow_mem1574, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1574_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_5_8]
  rfl
theorem row_eq8_1_5_9 : RadiusFivePruning.stateRow8_1_5_9 = ParentOwnership.parentRow1576 := by rfl
theorem patch_mem8_1_5_9 : RadiusFivePruning.patch8_1_5_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1576, parentRow_mem1576, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1576_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_5_9]
  rfl
theorem chunk_mem8_1_5 : ∀ p ∈ RadiusFivePruning.final8_1_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_1_5, List.forall_mem_cons]
  exact ⟨patch_mem8_1_5_0,⟨patch_mem8_1_5_1,⟨patch_mem8_1_5_2,⟨patch_mem8_1_5_3,⟨patch_mem8_1_5_4,⟨patch_mem8_1_5_5,⟨patch_mem8_1_5_6,⟨patch_mem8_1_5_7,⟨patch_mem8_1_5_8,⟨patch_mem8_1_5_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
