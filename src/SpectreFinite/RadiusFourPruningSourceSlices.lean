module

public import SpectreFinite.RadiusFourFamilyData
public import SpectreFinite.RadiusFourPruningRotationIndices

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def source0_0 : List Patch := ((RadiusFour.familyForKind 0).drop 0).take 12
def source0_1 : List Patch := ((RadiusFour.familyForKind 0).drop 12).take 12
def source0_2 : List Patch := ((RadiusFour.familyForKind 0).drop 24).take 12
theorem source0_split : [source0_0, source0_1, source0_2].flatten = RadiusFour.familyForKind 0 := by rfl
def source1_0 : List Patch := ((RadiusFour.familyForKind 1).drop 0).take 12
def source1_1 : List Patch := ((RadiusFour.familyForKind 1).drop 12).take 12
def source1_2 : List Patch := ((RadiusFour.familyForKind 1).drop 24).take 9
theorem source1_split : [source1_0, source1_1, source1_2].flatten = RadiusFour.familyForKind 1 := by rfl
def source2_0 : List Patch := ((RadiusFour.familyForKind 2).drop 0).take 8
theorem source2_split : [source2_0].flatten = RadiusFour.familyForKind 2 := by rfl
def source3_0 : List Patch := ((RadiusFour.familyForKind 3).drop 0).take 3
theorem source3_split : [source3_0].flatten = RadiusFour.familyForKind 3 := by rfl
def source4_0 : List Patch := ((RadiusFour.familyForKind 4).drop 0).take 12
def source4_1 : List Patch := ((RadiusFour.familyForKind 4).drop 12).take 12
def source4_2 : List Patch := ((RadiusFour.familyForKind 4).drop 24).take 4
theorem source4_split : [source4_0, source4_1, source4_2].flatten = RadiusFour.familyForKind 4 := by rfl
def source5_0 : List Patch := ((RadiusFour.familyForKind 5).drop 0).take 12
def source5_1 : List Patch := ((RadiusFour.familyForKind 5).drop 12).take 12
def source5_2 : List Patch := ((RadiusFour.familyForKind 5).drop 24).take 6
theorem source5_split : [source5_0, source5_1, source5_2].flatten = RadiusFour.familyForKind 5 := by rfl
def source6_0 : List Patch := ((RadiusFour.familyForKind 6).drop 0).take 12
def source6_1 : List Patch := ((RadiusFour.familyForKind 6).drop 12).take 12
def source6_2 : List Patch := ((RadiusFour.familyForKind 6).drop 24).take 12
def source6_3 : List Patch := ((RadiusFour.familyForKind 6).drop 36).take 8
theorem source6_split : [source6_0, source6_1, source6_2, source6_3].flatten = RadiusFour.familyForKind 6 := by rfl
def source7_0 : List Patch := ((RadiusFour.familyForKind 7).drop 0).take 12
def source7_1 : List Patch := ((RadiusFour.familyForKind 7).drop 12).take 12
def source7_2 : List Patch := ((RadiusFour.familyForKind 7).drop 24).take 12
def source7_3 : List Patch := ((RadiusFour.familyForKind 7).drop 36).take 12
def source7_4 : List Patch := ((RadiusFour.familyForKind 7).drop 48).take 12
def source7_5 : List Patch := ((RadiusFour.familyForKind 7).drop 60).take 12
def source7_6 : List Patch := ((RadiusFour.familyForKind 7).drop 72).take 8
theorem source7_split : [source7_0, source7_1, source7_2, source7_3, source7_4, source7_5, source7_6].flatten = RadiusFour.familyForKind 7 := by rfl
def source8_0 : List Patch := ((RadiusFour.familyForKind 8).drop 0).take 12
def source8_1 : List Patch := ((RadiusFour.familyForKind 8).drop 12).take 12
def source8_2 : List Patch := ((RadiusFour.familyForKind 8).drop 24).take 12
def source8_3 : List Patch := ((RadiusFour.familyForKind 8).drop 36).take 12
def source8_4 : List Patch := ((RadiusFour.familyForKind 8).drop 48).take 4
theorem source8_split : [source8_0, source8_1, source8_2, source8_3, source8_4].flatten = RadiusFour.familyForKind 8 := by rfl

theorem sourceStates0_0 : source0_0 = ((RadiusFour.root0Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates0_1 : source0_1 = ((RadiusFour.root0Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates0_2 : source0_2 = ((RadiusFour.root0Outputs.drop 24).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates1_0 : source1_0 = ((RadiusFour.root1Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates1_1 : source1_1 = ((RadiusFour.root1Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates1_2 : source1_2 = ((RadiusFour.root1Outputs.drop 24).take 9).map (List.zip literalDomain) := by rfl
theorem sourceStates2_0 : source2_0 = ((RadiusFour.root2Outputs.drop 0).take 8).map (List.zip literalDomain) := by rfl
theorem sourceStates3_0 : source3_0 = ((RadiusFour.root3Outputs.drop 0).take 3).map (List.zip literalDomain) := by rfl
theorem sourceStates4_0 : source4_0 = ((RadiusFour.root4Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates4_1 : source4_1 = ((RadiusFour.root4Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates4_2 : source4_2 = ((RadiusFour.root4Outputs.drop 24).take 4).map (List.zip literalDomain) := by rfl
theorem sourceStates5_0 : source5_0 = ((RadiusFour.root5Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates5_1 : source5_1 = ((RadiusFour.root5Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates5_2 : source5_2 = ((RadiusFour.root5Outputs.drop 24).take 6).map (List.zip literalDomain) := by rfl
theorem sourceStates6_0 : source6_0 = ((RadiusFour.root6Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates6_1 : source6_1 = ((RadiusFour.root6Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates6_2 : source6_2 = ((RadiusFour.root6Outputs.drop 24).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates6_3 : source6_3 = ((RadiusFour.root6Outputs.drop 36).take 8).map (List.zip literalDomain) := by rfl
theorem sourceStates7_0 : source7_0 = ((RadiusFour.root7Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_1 : source7_1 = ((RadiusFour.root7Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_2 : source7_2 = ((RadiusFour.root7Outputs.drop 24).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_3 : source7_3 = ((RadiusFour.root7Outputs.drop 36).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_4 : source7_4 = ((RadiusFour.root7Outputs.drop 48).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_5 : source7_5 = ((RadiusFour.root7Outputs.drop 60).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_6 : source7_6 = ((RadiusFour.root7Outputs.drop 72).take 8).map (List.zip literalDomain) := by rfl
theorem sourceStates8_0 : source8_0 = ((RadiusFour.root8Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates8_1 : source8_1 = ((RadiusFour.root8Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates8_2 : source8_2 = ((RadiusFour.root8Outputs.drop 24).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates8_3 : source8_3 = ((RadiusFour.root8Outputs.drop 36).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates8_4 : source8_4 = ((RadiusFour.root8Outputs.drop 48).take 4).map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFourPruning
