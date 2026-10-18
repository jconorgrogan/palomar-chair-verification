module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart020
public import SpectreFinite.ParentOwnershipFinitePart086
public import SpectreFinite.ParentOwnershipFinitePart087

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_2_1_0 : List State := ParentOwnership.parentRow0322
def patch7_2_1_0 : Patch := literalDomain.zip stateRow7_2_1_0
theorem patch_states7_2_1_0 : patch7_2_1_0.map Prod.snd = stateRow7_2_1_0 := by rfl
def stateRow7_2_1_2 : List State := ParentOwnership.parentRow1388
def patch7_2_1_2 : Patch := literalDomain.zip stateRow7_2_1_2
theorem patch_states7_2_1_2 : patch7_2_1_2.map Prod.snd = stateRow7_2_1_2 := by rfl
def stateRow7_2_1_3 : List State := ParentOwnership.parentRow1399
def patch7_2_1_3 : Patch := literalDomain.zip stateRow7_2_1_3
theorem patch_states7_2_1_3 : patch7_2_1_3.map Prod.snd = stateRow7_2_1_3 := by rfl
def stateRow7_2_1_4 : List State := ParentOwnership.parentRow1389
def patch7_2_1_4 : Patch := literalDomain.zip stateRow7_2_1_4
theorem patch_states7_2_1_4 : patch7_2_1_4.map Prod.snd = stateRow7_2_1_4 := by rfl
def stateRow7_2_1_5 : List State := ParentOwnership.parentRow1400
def patch7_2_1_5 : Patch := literalDomain.zip stateRow7_2_1_5
theorem patch_states7_2_1_5 : patch7_2_1_5.map Prod.snd = stateRow7_2_1_5 := by rfl
def stateRow7_2_1_6 : List State := ParentOwnership.parentRow1391
def patch7_2_1_6 : Patch := literalDomain.zip stateRow7_2_1_6
theorem patch_states7_2_1_6 : patch7_2_1_6.map Prod.snd = stateRow7_2_1_6 := by rfl
def stateRow7_2_1_9 : List State := ParentOwnership.parentRow1392
def patch7_2_1_9 : Patch := literalDomain.zip stateRow7_2_1_9
theorem patch_states7_2_1_9 : patch7_2_1_9.map Prod.snd = stateRow7_2_1_9 := by rfl
def stateRow7_2_1_10 : List State := ParentOwnership.parentRow1401
def patch7_2_1_10 : Patch := literalDomain.zip stateRow7_2_1_10
theorem patch_states7_2_1_10 : patch7_2_1_10.map Prod.snd = stateRow7_2_1_10 := by rfl
def stateRow7_2_1_11 : List State := ParentOwnership.parentRow0323
def patch7_2_1_11 : Patch := literalDomain.zip stateRow7_2_1_11
theorem patch_states7_2_1_11 : patch7_2_1_11.map Prod.snd = stateRow7_2_1_11 := by rfl
def final7_2_1 : List Patch := [patch7_2_1_0, patch7_2_1_2, patch7_2_1_3, patch7_2_1_4, patch7_2_1_5, patch7_2_1_6, patch7_2_1_9, patch7_2_1_10, patch7_2_1_11]
def stateRows7_2_1 : List (List State) := [stateRow7_2_1_0, stateRow7_2_1_2, stateRow7_2_1_3, stateRow7_2_1_4, stateRow7_2_1_5, stateRow7_2_1_6, stateRow7_2_1_9, stateRow7_2_1_10, stateRow7_2_1_11]
theorem stateRows_eq7_2_1 : stateRows7_2_1 = final7_2_1.map (List.map Prod.snd) := by
  simp only [stateRows7_2_1, final7_2_1, List.map_cons, List.map_nil, patch_states7_2_1_0, patch_states7_2_1_2, patch_states7_2_1_3, patch_states7_2_1_4, patch_states7_2_1_5, patch_states7_2_1_6, patch_states7_2_1_9, patch_states7_2_1_10, patch_states7_2_1_11]
theorem final_states7_2_1 : final7_2_1 = stateRows7_2_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
