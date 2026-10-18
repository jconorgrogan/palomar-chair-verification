module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart050
public import SpectreFinite.ParentOwnershipFinitePart130
public import SpectreFinite.ParentOwnershipFinitePart131

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_5_3_0 : List State := ParentOwnership.parentRow2099
def patch7_5_3_0 : Patch := literalDomain.zip stateRow7_5_3_0
theorem patch_states7_5_3_0 : patch7_5_3_0.map Prod.snd = stateRow7_5_3_0 := by rfl
def stateRow7_5_3_1 : List State := ParentOwnership.parentRow2101
def patch7_5_3_1 : Patch := literalDomain.zip stateRow7_5_3_1
theorem patch_states7_5_3_1 : patch7_5_3_1.map Prod.snd = stateRow7_5_3_1 := by rfl
def stateRow7_5_3_2 : List State := ParentOwnership.parentRow2100
def patch7_5_3_2 : Patch := literalDomain.zip stateRow7_5_3_2
theorem patch_states7_5_3_2 : patch7_5_3_2.map Prod.snd = stateRow7_5_3_2 := by rfl
def stateRow7_5_3_3 : List State := ParentOwnership.parentRow2102
def patch7_5_3_3 : Patch := literalDomain.zip stateRow7_5_3_3
theorem patch_states7_5_3_3 : patch7_5_3_3.map Prod.snd = stateRow7_5_3_3 := by rfl
def stateRow7_5_3_5 : List State := ParentOwnership.parentRow0810
def patch7_5_3_5 : Patch := literalDomain.zip stateRow7_5_3_5
theorem patch_states7_5_3_5 : patch7_5_3_5.map Prod.snd = stateRow7_5_3_5 := by rfl
def stateRow7_5_3_6 : List State := ParentOwnership.parentRow0809
def patch7_5_3_6 : Patch := literalDomain.zip stateRow7_5_3_6
theorem patch_states7_5_3_6 : patch7_5_3_6.map Prod.snd = stateRow7_5_3_6 := by rfl
def stateRow7_5_3_7 : List State := ParentOwnership.parentRow2092
def patch7_5_3_7 : Patch := literalDomain.zip stateRow7_5_3_7
theorem patch_states7_5_3_7 : patch7_5_3_7.map Prod.snd = stateRow7_5_3_7 := by rfl
def stateRow7_5_3_8 : List State := ParentOwnership.parentRow2093
def patch7_5_3_8 : Patch := literalDomain.zip stateRow7_5_3_8
theorem patch_states7_5_3_8 : patch7_5_3_8.map Prod.snd = stateRow7_5_3_8 := by rfl
def stateRow7_5_3_9 : List State := ParentOwnership.parentRow2095
def patch7_5_3_9 : Patch := literalDomain.zip stateRow7_5_3_9
theorem patch_states7_5_3_9 : patch7_5_3_9.map Prod.snd = stateRow7_5_3_9 := by rfl
def stateRow7_5_3_10 : List State := ParentOwnership.parentRow2094
def patch7_5_3_10 : Patch := literalDomain.zip stateRow7_5_3_10
theorem patch_states7_5_3_10 : patch7_5_3_10.map Prod.snd = stateRow7_5_3_10 := by rfl
def stateRow7_5_3_11 : List State := ParentOwnership.parentRow0804
def patch7_5_3_11 : Patch := literalDomain.zip stateRow7_5_3_11
theorem patch_states7_5_3_11 : patch7_5_3_11.map Prod.snd = stateRow7_5_3_11 := by rfl
def final7_5_3 : List Patch := [patch7_5_3_0, patch7_5_3_1, patch7_5_3_2, patch7_5_3_3, patch7_5_3_5, patch7_5_3_6, patch7_5_3_7, patch7_5_3_8, patch7_5_3_9, patch7_5_3_10, patch7_5_3_11]
def stateRows7_5_3 : List (List State) := [stateRow7_5_3_0, stateRow7_5_3_1, stateRow7_5_3_2, stateRow7_5_3_3, stateRow7_5_3_5, stateRow7_5_3_6, stateRow7_5_3_7, stateRow7_5_3_8, stateRow7_5_3_9, stateRow7_5_3_10, stateRow7_5_3_11]
theorem stateRows_eq7_5_3 : stateRows7_5_3 = final7_5_3.map (List.map Prod.snd) := by
  simp only [stateRows7_5_3, final7_5_3, List.map_cons, List.map_nil, patch_states7_5_3_0, patch_states7_5_3_1, patch_states7_5_3_2, patch_states7_5_3_3, patch_states7_5_3_5, patch_states7_5_3_6, patch_states7_5_3_7, patch_states7_5_3_8, patch_states7_5_3_9, patch_states7_5_3_10, patch_states7_5_3_11]
theorem final_states7_5_3 : final7_5_3 = stateRows7_5_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
