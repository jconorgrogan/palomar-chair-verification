module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart023
public import SpectreFinite.ParentOwnershipFinitePart037
public import SpectreFinite.ParentOwnershipFinitePart091

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow3_5_0_1 : List State := ParentOwnership.parentRow1466
def patch3_5_0_1 : Patch := literalDomain.zip stateRow3_5_0_1
theorem patch_states3_5_0_1 : patch3_5_0_1.map Prod.snd = stateRow3_5_0_1 := by rfl
def stateRow3_5_0_3 : List State := ParentOwnership.parentRow0369
def patch3_5_0_3 : Patch := literalDomain.zip stateRow3_5_0_3
theorem patch_states3_5_0_3 : patch3_5_0_3.map Prod.snd = stateRow3_5_0_3 := by rfl
def stateRow3_5_0_4 : List State := ParentOwnership.parentRow0595
def patch3_5_0_4 : Patch := literalDomain.zip stateRow3_5_0_4
theorem patch_states3_5_0_4 : patch3_5_0_4.map Prod.snd = stateRow3_5_0_4 := by rfl
def stateRow3_5_0_5 : List State := ParentOwnership.parentRow1467
def patch3_5_0_5 : Patch := literalDomain.zip stateRow3_5_0_5
theorem patch_states3_5_0_5 : patch3_5_0_5.map Prod.snd = stateRow3_5_0_5 := by rfl
def stateRow3_5_0_6 : List State := ParentOwnership.parentRow1468
def patch3_5_0_6 : Patch := literalDomain.zip stateRow3_5_0_6
theorem patch_states3_5_0_6 : patch3_5_0_6.map Prod.snd = stateRow3_5_0_6 := by rfl
def final3_5_0 : List Patch := [patch3_5_0_1, patch3_5_0_3, patch3_5_0_4, patch3_5_0_5, patch3_5_0_6]
def stateRows3_5_0 : List (List State) := [stateRow3_5_0_1, stateRow3_5_0_3, stateRow3_5_0_4, stateRow3_5_0_5, stateRow3_5_0_6]
theorem stateRows_eq3_5_0 : stateRows3_5_0 = final3_5_0.map (List.map Prod.snd) := by
  simp only [stateRows3_5_0, final3_5_0, List.map_cons, List.map_nil, patch_states3_5_0_1, patch_states3_5_0_3, patch_states3_5_0_4, patch_states3_5_0_5, patch_states3_5_0_6]
theorem final_states3_5_0 : final3_5_0 = stateRows3_5_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
