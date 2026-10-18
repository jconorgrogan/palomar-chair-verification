module

public import SpectreFinite.RadiusFiveParentRowMembership
public import SpectreFinite.RadiusFiveParentBindingDomain
public import SpectreFinite.RadiusFivePruningLiteralBlock8T0C4
public import SpectreFinite.RadiusFivePruningLiteralBlock8T0C5
public import SpectreFinite.RadiusFivePruningLiteralBlock8T1C0
public import SpectreFinite.RadiusFivePruningLiteralBlock8T1C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem row_eq8_0_4_0 : RadiusFivePruning.stateRow8_0_4_0 = ParentOwnership.parentRow0612 := by rfl
theorem patch_mem8_0_4_0 : RadiusFivePruning.patch8_0_4_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0612, parentRow_mem0612, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0612_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_4_0]
  rfl
theorem row_eq8_0_4_1 : RadiusFivePruning.stateRow8_0_4_1 = ParentOwnership.parentRow1653 := by rfl
theorem patch_mem8_0_4_1 : RadiusFivePruning.patch8_0_4_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1653, parentRow_mem1653, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1653_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_4_1]
  rfl
theorem row_eq8_0_4_2 : RadiusFivePruning.stateRow8_0_4_2 = ParentOwnership.parentRow1654 := by rfl
theorem patch_mem8_0_4_2 : RadiusFivePruning.patch8_0_4_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1654, parentRow_mem1654, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1654_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_4_2]
  rfl
theorem row_eq8_0_4_3 : RadiusFivePruning.stateRow8_0_4_3 = ParentOwnership.parentRow1655 := by rfl
theorem patch_mem8_0_4_3 : RadiusFivePruning.patch8_0_4_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1655, parentRow_mem1655, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1655_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_4_3]
  rfl
theorem row_eq8_0_4_4 : RadiusFivePruning.stateRow8_0_4_4 = ParentOwnership.parentRow1656 := by rfl
theorem patch_mem8_0_4_4 : RadiusFivePruning.patch8_0_4_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1656, parentRow_mem1656, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1656_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_4_4]
  rfl
theorem row_eq8_0_4_5 : RadiusFivePruning.stateRow8_0_4_5 = ParentOwnership.parentRow1651 := by rfl
theorem patch_mem8_0_4_5 : RadiusFivePruning.patch8_0_4_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1651, parentRow_mem1651, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1651_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_4_5]
  rfl
theorem row_eq8_0_4_8 : RadiusFivePruning.stateRow8_0_4_8 = ParentOwnership.parentRow1652 := by rfl
theorem patch_mem8_0_4_8 : RadiusFivePruning.patch8_0_4_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1652, parentRow_mem1652, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1652_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_4_8]
  rfl
theorem row_eq8_0_4_9 : RadiusFivePruning.stateRow8_0_4_9 = ParentOwnership.parentRow1657 := by rfl
theorem patch_mem8_0_4_9 : RadiusFivePruning.patch8_0_4_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1657, parentRow_mem1657, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1657_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_4_9]
  rfl
theorem row_eq8_0_4_10 : RadiusFivePruning.stateRow8_0_4_10 = ParentOwnership.parentRow1658 := by rfl
theorem patch_mem8_0_4_10 : RadiusFivePruning.patch8_0_4_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1658, parentRow_mem1658, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1658_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_4_10]
  rfl
theorem row_eq8_0_4_11 : RadiusFivePruning.stateRow8_0_4_11 = ParentOwnership.parentRow1659 := by rfl
theorem patch_mem8_0_4_11 : RadiusFivePruning.patch8_0_4_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1659, parentRow_mem1659, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1659_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_4_11]
  rfl
theorem chunk_mem8_0_4 : ∀ p ∈ RadiusFivePruning.final8_0_4, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_0_4, List.forall_mem_cons]
  exact ⟨patch_mem8_0_4_0,⟨patch_mem8_0_4_1,⟨patch_mem8_0_4_2,⟨patch_mem8_0_4_3,⟨patch_mem8_0_4_4,⟨patch_mem8_0_4_5,⟨patch_mem8_0_4_8,⟨patch_mem8_0_4_9,⟨patch_mem8_0_4_10,⟨patch_mem8_0_4_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_0_5_0 : RadiusFivePruning.stateRow8_0_5_0 = ParentOwnership.parentRow1660 := by rfl
theorem patch_mem8_0_5_0 : RadiusFivePruning.patch8_0_5_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1660, parentRow_mem1660, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1660_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_5_0]
  rfl
theorem row_eq8_0_5_1 : RadiusFivePruning.stateRow8_0_5_1 = ParentOwnership.parentRow1661 := by rfl
theorem patch_mem8_0_5_1 : RadiusFivePruning.patch8_0_5_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1661, parentRow_mem1661, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1661_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_5_1]
  rfl
theorem row_eq8_0_5_2 : RadiusFivePruning.stateRow8_0_5_2 = ParentOwnership.parentRow1662 := by rfl
theorem patch_mem8_0_5_2 : RadiusFivePruning.patch8_0_5_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1662, parentRow_mem1662, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1662_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_5_2]
  rfl
theorem row_eq8_0_5_3 : RadiusFivePruning.stateRow8_0_5_3 = ParentOwnership.parentRow1663 := by rfl
theorem patch_mem8_0_5_3 : RadiusFivePruning.patch8_0_5_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1663, parentRow_mem1663, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1663_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_5_3]
  rfl
theorem row_eq8_0_5_4 : RadiusFivePruning.stateRow8_0_5_4 = ParentOwnership.parentRow1670 := by rfl
theorem patch_mem8_0_5_4 : RadiusFivePruning.patch8_0_5_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1670, parentRow_mem1670, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1670_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_5_4]
  rfl
theorem row_eq8_0_5_5 : RadiusFivePruning.stateRow8_0_5_5 = ParentOwnership.parentRow1671 := by rfl
theorem patch_mem8_0_5_5 : RadiusFivePruning.patch8_0_5_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1671, parentRow_mem1671, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1671_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_5_5]
  rfl
theorem row_eq8_0_5_6 : RadiusFivePruning.stateRow8_0_5_6 = ParentOwnership.parentRow1672 := by rfl
theorem patch_mem8_0_5_6 : RadiusFivePruning.patch8_0_5_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1672, parentRow_mem1672, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1672_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_5_6]
  rfl
theorem row_eq8_0_5_7 : RadiusFivePruning.stateRow8_0_5_7 = ParentOwnership.parentRow1673 := by rfl
theorem patch_mem8_0_5_7 : RadiusFivePruning.patch8_0_5_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1673, parentRow_mem1673, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1673_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_5_7]
  rfl
theorem row_eq8_0_5_8 : RadiusFivePruning.stateRow8_0_5_8 = ParentOwnership.parentRow1674 := by rfl
theorem patch_mem8_0_5_8 : RadiusFivePruning.patch8_0_5_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1674, parentRow_mem1674, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1674_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_5_8]
  rfl
theorem row_eq8_0_5_9 : RadiusFivePruning.stateRow8_0_5_9 = ParentOwnership.parentRow1675 := by rfl
theorem patch_mem8_0_5_9 : RadiusFivePruning.patch8_0_5_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1675, parentRow_mem1675, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1675_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_0_5_9]
  rfl
theorem chunk_mem8_0_5 : ∀ p ∈ RadiusFivePruning.final8_0_5, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_0_5, List.forall_mem_cons]
  exact ⟨patch_mem8_0_5_0,⟨patch_mem8_0_5_1,⟨patch_mem8_0_5_2,⟨patch_mem8_0_5_3,⟨patch_mem8_0_5_4,⟨patch_mem8_0_5_5,⟨patch_mem8_0_5_6,⟨patch_mem8_0_5_7,⟨patch_mem8_0_5_8,⟨patch_mem8_0_5_9,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_1_0_1 : RadiusFivePruning.stateRow8_1_0_1 = ParentOwnership.parentRow1997 := by rfl
theorem patch_mem8_1_0_1 : RadiusFivePruning.patch8_1_0_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1997, parentRow_mem1997, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1997_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_0_1]
  rfl
theorem row_eq8_1_0_3 : RadiusFivePruning.stateRow8_1_0_3 = ParentOwnership.parentRow0934 := by rfl
theorem patch_mem8_1_0_3 : RadiusFivePruning.patch8_1_0_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow0934, parentRow_mem0934, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow0934_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_0_3]
  rfl
theorem row_eq8_1_0_4 : RadiusFivePruning.stateRow8_1_0_4 = ParentOwnership.parentRow1998 := by rfl
theorem patch_mem8_1_0_4 : RadiusFivePruning.patch8_1_0_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1998, parentRow_mem1998, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1998_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_0_4]
  rfl
theorem row_eq8_1_0_5 : RadiusFivePruning.stateRow8_1_0_5 = ParentOwnership.parentRow1999 := by rfl
theorem patch_mem8_1_0_5 : RadiusFivePruning.patch8_1_0_5 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1999, parentRow_mem1999, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1999_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_0_5]
  rfl
theorem row_eq8_1_0_6 : RadiusFivePruning.stateRow8_1_0_6 = ParentOwnership.parentRow2000 := by rfl
theorem patch_mem8_1_0_6 : RadiusFivePruning.patch8_1_0_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow2000, parentRow_mem2000, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow2000_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_0_6]
  rfl
theorem row_eq8_1_0_7 : RadiusFivePruning.stateRow8_1_0_7 = ParentOwnership.parentRow1971 := by rfl
theorem patch_mem8_1_0_7 : RadiusFivePruning.patch8_1_0_7 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1971, parentRow_mem1971, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1971_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_0_7]
  rfl
theorem row_eq8_1_0_8 : RadiusFivePruning.stateRow8_1_0_8 = ParentOwnership.parentRow1976 := by rfl
theorem patch_mem8_1_0_8 : RadiusFivePruning.patch8_1_0_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1976, parentRow_mem1976, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1976_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_0_8]
  rfl
theorem row_eq8_1_0_9 : RadiusFivePruning.stateRow8_1_0_9 = ParentOwnership.parentRow1963 := by rfl
theorem patch_mem8_1_0_9 : RadiusFivePruning.patch8_1_0_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1963, parentRow_mem1963, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1963_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_0_9]
  rfl
theorem row_eq8_1_0_10 : RadiusFivePruning.stateRow8_1_0_10 = ParentOwnership.parentRow1972 := by rfl
theorem patch_mem8_1_0_10 : RadiusFivePruning.patch8_1_0_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1972, parentRow_mem1972, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1972_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_0_10]
  rfl
theorem row_eq8_1_0_11 : RadiusFivePruning.stateRow8_1_0_11 = ParentOwnership.parentRow1964 := by rfl
theorem patch_mem8_1_0_11 : RadiusFivePruning.patch8_1_0_11 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1964, parentRow_mem1964, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1964_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_0_11]
  rfl
theorem chunk_mem8_1_0 : ∀ p ∈ RadiusFivePruning.final8_1_0, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_1_0, List.forall_mem_cons]
  exact ⟨patch_mem8_1_0_1,⟨patch_mem8_1_0_3,⟨patch_mem8_1_0_4,⟨patch_mem8_1_0_5,⟨patch_mem8_1_0_6,⟨patch_mem8_1_0_7,⟨patch_mem8_1_0_8,⟨patch_mem8_1_0_9,⟨patch_mem8_1_0_10,⟨patch_mem8_1_0_11,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem row_eq8_1_1_0 : RadiusFivePruning.stateRow8_1_1_0 = ParentOwnership.parentRow1965 := by rfl
theorem patch_mem8_1_1_0 : RadiusFivePruning.patch8_1_1_0 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1965, parentRow_mem1965, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1965_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_1_0]
  rfl
theorem row_eq8_1_1_1 : RadiusFivePruning.stateRow8_1_1_1 = ParentOwnership.parentRow1968 := by rfl
theorem patch_mem8_1_1_1 : RadiusFivePruning.patch8_1_1_1 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1968, parentRow_mem1968, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1968_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_1_1]
  rfl
theorem row_eq8_1_1_2 : RadiusFivePruning.stateRow8_1_1_2 = ParentOwnership.parentRow1973 := by rfl
theorem patch_mem8_1_1_2 : RadiusFivePruning.patch8_1_1_2 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1973, parentRow_mem1973, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1973_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_1_2]
  rfl
theorem row_eq8_1_1_3 : RadiusFivePruning.stateRow8_1_1_3 = ParentOwnership.parentRow1966 := by rfl
theorem patch_mem8_1_1_3 : RadiusFivePruning.patch8_1_1_3 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1966, parentRow_mem1966, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1966_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_1_3]
  rfl
theorem row_eq8_1_1_4 : RadiusFivePruning.stateRow8_1_1_4 = ParentOwnership.parentRow1967 := by rfl
theorem patch_mem8_1_1_4 : RadiusFivePruning.patch8_1_1_4 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1967, parentRow_mem1967, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1967_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_1_4]
  rfl
theorem row_eq8_1_1_6 : RadiusFivePruning.stateRow8_1_1_6 = ParentOwnership.parentRow1969 := by rfl
theorem patch_mem8_1_1_6 : RadiusFivePruning.patch8_1_1_6 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1969, parentRow_mem1969, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1969_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_1_6]
  rfl
theorem row_eq8_1_1_8 : RadiusFivePruning.stateRow8_1_1_8 = ParentOwnership.parentRow1974 := by rfl
theorem patch_mem8_1_1_8 : RadiusFivePruning.patch8_1_1_8 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1974, parentRow_mem1974, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1974_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_1_8]
  rfl
theorem row_eq8_1_1_9 : RadiusFivePruning.stateRow8_1_1_9 = ParentOwnership.parentRow1970 := by rfl
theorem patch_mem8_1_1_9 : RadiusFivePruning.patch8_1_1_9 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1970, parentRow_mem1970, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1970_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_1_9]
  rfl
theorem row_eq8_1_1_10 : RadiusFivePruning.stateRow8_1_1_10 = ParentOwnership.parentRow1975 := by rfl
theorem patch_mem8_1_1_10 : RadiusFivePruning.patch8_1_1_10 ∈ ParentOwnership.certifiedParentFamily := by
  apply List.mem_map.mpr
  refine ⟨ParentOwnership.parentRow1975, parentRow_mem1975, ?_⟩
  rw [ParentOwnership.encodedPatch_eq_zip _ ParentOwnership.parentRow1975_property.1, ← literalDomain_eq_hexRegion, ← row_eq8_1_1_10]
  rfl
theorem chunk_mem8_1_1 : ∀ p ∈ RadiusFivePruning.final8_1_1, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [RadiusFivePruning.final8_1_1, List.forall_mem_cons]
  exact ⟨patch_mem8_1_1_0,⟨patch_mem8_1_1_1,⟨patch_mem8_1_1_2,⟨patch_mem8_1_1_3,⟨patch_mem8_1_1_4,⟨patch_mem8_1_1_6,⟨patch_mem8_1_1_8,⟨patch_mem8_1_1_9,⟨patch_mem8_1_1_10,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩

end SpectreFinite.HexSearch.RadiusFiveParentBinding
