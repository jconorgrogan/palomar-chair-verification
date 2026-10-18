module

public import SpectreFinite.RadiusFiveFamilyData
public import SpectreFinite.RadiusFivePruningRotationIndices

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def source0_0 : List Patch := ((RadiusFive.familyForKind 0).drop 0).take 12
def source0_1 : List Patch := ((RadiusFive.familyForKind 0).drop 12).take 12
def source0_2 : List Patch := ((RadiusFive.familyForKind 0).drop 24).take 12
def source0_3 : List Patch := ((RadiusFive.familyForKind 0).drop 36).take 12
def source0_4 : List Patch := ((RadiusFive.familyForKind 0).drop 48).take 12
theorem source0_split : [source0_0, source0_1, source0_2, source0_3, source0_4].flatten = RadiusFive.familyForKind 0 := by rfl
def source1_0 : List Patch := ((RadiusFive.familyForKind 1).drop 0).take 12
def source1_1 : List Patch := ((RadiusFive.familyForKind 1).drop 12).take 12
def source1_2 : List Patch := ((RadiusFive.familyForKind 1).drop 24).take 12
def source1_3 : List Patch := ((RadiusFive.familyForKind 1).drop 36).take 12
def source1_4 : List Patch := ((RadiusFive.familyForKind 1).drop 48).take 11
theorem source1_split : [source1_0, source1_1, source1_2, source1_3, source1_4].flatten = RadiusFive.familyForKind 1 := by rfl
def source2_0 : List Patch := ((RadiusFive.familyForKind 2).drop 0).take 6
theorem source2_split : [source2_0].flatten = RadiusFive.familyForKind 2 := by rfl
def source3_0 : List Patch := ((RadiusFive.familyForKind 3).drop 0).take 7
theorem source3_split : [source3_0].flatten = RadiusFive.familyForKind 3 := by rfl
def source4_0 : List Patch := ((RadiusFive.familyForKind 4).drop 0).take 12
def source4_1 : List Patch := ((RadiusFive.familyForKind 4).drop 12).take 12
def source4_2 : List Patch := ((RadiusFive.familyForKind 4).drop 24).take 12
def source4_3 : List Patch := ((RadiusFive.familyForKind 4).drop 36).take 11
theorem source4_split : [source4_0, source4_1, source4_2, source4_3].flatten = RadiusFive.familyForKind 4 := by rfl
def source5_0 : List Patch := ((RadiusFive.familyForKind 5).drop 0).take 12
def source5_1 : List Patch := ((RadiusFive.familyForKind 5).drop 12).take 12
def source5_2 : List Patch := ((RadiusFive.familyForKind 5).drop 24).take 12
theorem source5_split : [source5_0, source5_1, source5_2].flatten = RadiusFive.familyForKind 5 := by rfl
def source6_0 : List Patch := ((RadiusFive.familyForKind 6).drop 0).take 12
def source6_1 : List Patch := ((RadiusFive.familyForKind 6).drop 12).take 12
def source6_2 : List Patch := ((RadiusFive.familyForKind 6).drop 24).take 12
def source6_3 : List Patch := ((RadiusFive.familyForKind 6).drop 36).take 12
def source6_4 : List Patch := ((RadiusFive.familyForKind 6).drop 48).take 12
def source6_5 : List Patch := ((RadiusFive.familyForKind 6).drop 60).take 3
theorem source6_split : [source6_0, source6_1, source6_2, source6_3, source6_4, source6_5].flatten = RadiusFive.familyForKind 6 := by rfl
def source7_0 : List Patch := ((RadiusFive.familyForKind 7).drop 0).take 12
def source7_1 : List Patch := ((RadiusFive.familyForKind 7).drop 12).take 12
def source7_2 : List Patch := ((RadiusFive.familyForKind 7).drop 24).take 12
def source7_3 : List Patch := ((RadiusFive.familyForKind 7).drop 36).take 12
def source7_4 : List Patch := ((RadiusFive.familyForKind 7).drop 48).take 12
def source7_5 : List Patch := ((RadiusFive.familyForKind 7).drop 60).take 12
def source7_6 : List Patch := ((RadiusFive.familyForKind 7).drop 72).take 12
def source7_7 : List Patch := ((RadiusFive.familyForKind 7).drop 84).take 12
def source7_8 : List Patch := ((RadiusFive.familyForKind 7).drop 96).take 10
theorem source7_split : [source7_0, source7_1, source7_2, source7_3, source7_4, source7_5, source7_6, source7_7, source7_8].flatten = RadiusFive.familyForKind 7 := by rfl
def source8_0 : List Patch := ((RadiusFive.familyForKind 8).drop 0).take 12
def source8_1 : List Patch := ((RadiusFive.familyForKind 8).drop 12).take 12
def source8_2 : List Patch := ((RadiusFive.familyForKind 8).drop 24).take 12
def source8_3 : List Patch := ((RadiusFive.familyForKind 8).drop 36).take 12
def source8_4 : List Patch := ((RadiusFive.familyForKind 8).drop 48).take 12
def source8_5 : List Patch := ((RadiusFive.familyForKind 8).drop 60).take 10
theorem source8_split : [source8_0, source8_1, source8_2, source8_3, source8_4, source8_5].flatten = RadiusFive.familyForKind 8 := by rfl

theorem sourceStates0_0 : source0_0 = ((RadiusFive.root0Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates0_1 : source0_1 = ((RadiusFive.root0Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates0_2 : source0_2 = ((RadiusFive.root0Outputs.drop 24).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates0_3 : source0_3 = ((RadiusFive.root0Outputs.drop 36).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates0_4 : source0_4 = ((RadiusFive.root0Outputs.drop 48).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates1_0 : source1_0 = ((RadiusFive.root1Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates1_1 : source1_1 = ((RadiusFive.root1Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates1_2 : source1_2 = ((RadiusFive.root1Outputs.drop 24).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates1_3 : source1_3 = ((RadiusFive.root1Outputs.drop 36).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates1_4 : source1_4 = ((RadiusFive.root1Outputs.drop 48).take 11).map (List.zip literalDomain) := by rfl
theorem sourceStates2_0 : source2_0 = ((RadiusFive.root2Outputs.drop 0).take 6).map (List.zip literalDomain) := by rfl
theorem sourceStates3_0 : source3_0 = ((RadiusFive.root3Outputs.drop 0).take 7).map (List.zip literalDomain) := by rfl
theorem sourceStates4_0 : source4_0 = ((RadiusFive.root4Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates4_1 : source4_1 = ((RadiusFive.root4Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates4_2 : source4_2 = ((RadiusFive.root4Outputs.drop 24).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates4_3 : source4_3 = ((RadiusFive.root4Outputs.drop 36).take 11).map (List.zip literalDomain) := by rfl
theorem sourceStates5_0 : source5_0 = ((RadiusFive.root5Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates5_1 : source5_1 = ((RadiusFive.root5Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates5_2 : source5_2 = ((RadiusFive.root5Outputs.drop 24).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates6_0 : source6_0 = ((RadiusFive.root6Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates6_1 : source6_1 = ((RadiusFive.root6Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates6_2 : source6_2 = ((RadiusFive.root6Outputs.drop 24).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates6_3 : source6_3 = ((RadiusFive.root6Outputs.drop 36).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates6_4 : source6_4 = ((RadiusFive.root6Outputs.drop 48).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates6_5 : source6_5 = ((RadiusFive.root6Outputs.drop 60).take 3).map (List.zip literalDomain) := by rfl
theorem sourceStates7_0 : source7_0 = ((RadiusFive.root7Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_1 : source7_1 = ((RadiusFive.root7Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_2 : source7_2 = ((RadiusFive.root7Outputs.drop 24).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_3 : source7_3 = ((RadiusFive.root7Outputs.drop 36).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_4 : source7_4 = ((RadiusFive.root7Outputs.drop 48).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_5 : source7_5 = ((RadiusFive.root7Outputs.drop 60).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_6 : source7_6 = ((RadiusFive.root7Outputs.drop 72).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_7 : source7_7 = ((RadiusFive.root7Outputs.drop 84).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates7_8 : source7_8 = ((RadiusFive.root7Outputs.drop 96).take 10).map (List.zip literalDomain) := by rfl
theorem sourceStates8_0 : source8_0 = ((RadiusFive.root8Outputs.drop 0).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates8_1 : source8_1 = ((RadiusFive.root8Outputs.drop 12).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates8_2 : source8_2 = ((RadiusFive.root8Outputs.drop 24).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates8_3 : source8_3 = ((RadiusFive.root8Outputs.drop 36).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates8_4 : source8_4 = ((RadiusFive.root8Outputs.drop 48).take 12).map (List.zip literalDomain) := by rfl
theorem sourceStates8_5 : source8_5 = ((RadiusFive.root8Outputs.drop 60).take 10).map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
