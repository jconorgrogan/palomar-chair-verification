module

public import SpectreFinite.RadiusThreeFamilyData

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def source0_0 : List Patch := ((RadiusThree.familyForKind 0).drop 0).take 12
def source0_1 : List Patch := ((RadiusThree.familyForKind 0).drop 12).take 10
theorem source0_split : [source0_0, source0_1].flatten = RadiusThree.familyForKind 0 := by rfl
def source1_0 : List Patch := ((RadiusThree.familyForKind 1).drop 0).take 12
def source1_1 : List Patch := ((RadiusThree.familyForKind 1).drop 12).take 12
def source1_2 : List Patch := ((RadiusThree.familyForKind 1).drop 24).take 2
theorem source1_split : [source1_0, source1_1, source1_2].flatten = RadiusThree.familyForKind 1 := by rfl
def source2_0 : List Patch := ((RadiusThree.familyForKind 2).drop 0).take 1
theorem source2_split : [source2_0].flatten = RadiusThree.familyForKind 2 := by rfl
def source3_0 : List Patch := ((RadiusThree.familyForKind 3).drop 0).take 2
theorem source3_split : [source3_0].flatten = RadiusThree.familyForKind 3 := by rfl
def source4_0 : List Patch := ((RadiusThree.familyForKind 4).drop 0).take 12
def source4_1 : List Patch := ((RadiusThree.familyForKind 4).drop 12).take 10
theorem source4_split : [source4_0, source4_1].flatten = RadiusThree.familyForKind 4 := by rfl
def source5_0 : List Patch := ((RadiusThree.familyForKind 5).drop 0).take 12
def source5_1 : List Patch := ((RadiusThree.familyForKind 5).drop 12).take 12
def source5_2 : List Patch := ((RadiusThree.familyForKind 5).drop 24).take 1
theorem source5_split : [source5_0, source5_1, source5_2].flatten = RadiusThree.familyForKind 5 := by rfl
def source6_0 : List Patch := ((RadiusThree.familyForKind 6).drop 0).take 12
def source6_1 : List Patch := ((RadiusThree.familyForKind 6).drop 12).take 11
theorem source6_split : [source6_0, source6_1].flatten = RadiusThree.familyForKind 6 := by rfl
def source7_0 : List Patch := ((RadiusThree.familyForKind 7).drop 0).take 12
def source7_1 : List Patch := ((RadiusThree.familyForKind 7).drop 12).take 12
def source7_2 : List Patch := ((RadiusThree.familyForKind 7).drop 24).take 12
def source7_3 : List Patch := ((RadiusThree.familyForKind 7).drop 36).take 12
theorem source7_split : [source7_0, source7_1, source7_2, source7_3].flatten = RadiusThree.familyForKind 7 := by rfl
def source8_0 : List Patch := ((RadiusThree.familyForKind 8).drop 0).take 12
def source8_1 : List Patch := ((RadiusThree.familyForKind 8).drop 12).take 12
def source8_2 : List Patch := ((RadiusThree.familyForKind 8).drop 24).take 12
def source8_3 : List Patch := ((RadiusThree.familyForKind 8).drop 36).take 2
theorem source8_split : [source8_0, source8_1, source8_2, source8_3].flatten = RadiusThree.familyForKind 8 := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
