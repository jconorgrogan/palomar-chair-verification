module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart047
public import SpectreFinite.ParentOwnershipFinitePart123

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow3_1_0_1 : List State := ParentOwnership.parentRow0752
def patch3_1_0_1 : Patch := literalDomain.zip stateRow3_1_0_1
theorem patch_states3_1_0_1 : patch3_1_0_1.map Prod.snd = stateRow3_1_0_1 := by rfl
def stateRow3_1_0_3 : List State := ParentOwnership.parentRow1977
def patch3_1_0_3 : Patch := literalDomain.zip stateRow3_1_0_3
theorem patch_states3_1_0_3 : patch3_1_0_3.map Prod.snd = stateRow3_1_0_3 := by rfl
def stateRow3_1_0_4 : List State := ParentOwnership.parentRow1978
def patch3_1_0_4 : Patch := literalDomain.zip stateRow3_1_0_4
theorem patch_states3_1_0_4 : patch3_1_0_4.map Prod.snd = stateRow3_1_0_4 := by rfl
def stateRow3_1_0_5 : List State := ParentOwnership.parentRow1979
def patch3_1_0_5 : Patch := literalDomain.zip stateRow3_1_0_5
theorem patch_states3_1_0_5 : patch3_1_0_5.map Prod.snd = stateRow3_1_0_5 := by rfl
def stateRow3_1_0_6 : List State := ParentOwnership.parentRow1980
def patch3_1_0_6 : Patch := literalDomain.zip stateRow3_1_0_6
theorem patch_states3_1_0_6 : patch3_1_0_6.map Prod.snd = stateRow3_1_0_6 := by rfl
def final3_1_0 : List Patch := [patch3_1_0_1, patch3_1_0_3, patch3_1_0_4, patch3_1_0_5, patch3_1_0_6]
def stateRows3_1_0 : List (List State) := [stateRow3_1_0_1, stateRow3_1_0_3, stateRow3_1_0_4, stateRow3_1_0_5, stateRow3_1_0_6]
theorem stateRows_eq3_1_0 : stateRows3_1_0 = final3_1_0.map (List.map Prod.snd) := by
  simp only [stateRows3_1_0, final3_1_0, List.map_cons, List.map_nil, patch_states3_1_0_1, patch_states3_1_0_3, patch_states3_1_0_4, patch_states3_1_0_5, patch_states3_1_0_6]
theorem final_states3_1_0 : final3_1_0 = stateRows3_1_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
