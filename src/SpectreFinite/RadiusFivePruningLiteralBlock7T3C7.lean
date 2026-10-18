module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart002
public import SpectreFinite.ParentOwnershipFinitePart003
public import SpectreFinite.ParentOwnershipFinitePart077
public import SpectreFinite.ParentOwnershipFinitePart078

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_3_7_0 : List State := ParentOwnership.parentRow0037
def patch7_3_7_0 : Patch := literalDomain.zip stateRow7_3_7_0
theorem patch_states7_3_7_0 : patch7_3_7_0.map Prod.snd = stateRow7_3_7_0 := by rfl
def stateRow7_3_7_1 : List State := ParentOwnership.parentRow1233
def patch7_3_7_1 : Patch := literalDomain.zip stateRow7_3_7_1
theorem patch_states7_3_7_1 : patch7_3_7_1.map Prod.snd = stateRow7_3_7_1 := by rfl
def stateRow7_3_7_2 : List State := ParentOwnership.parentRow1247
def patch7_3_7_2 : Patch := literalDomain.zip stateRow7_3_7_2
theorem patch_states7_3_7_2 : patch7_3_7_2.map Prod.snd = stateRow7_3_7_2 := by rfl
def stateRow7_3_7_3 : List State := ParentOwnership.parentRow1234
def patch7_3_7_3 : Patch := literalDomain.zip stateRow7_3_7_3
theorem patch_states7_3_7_3 : patch7_3_7_3.map Prod.snd = stateRow7_3_7_3 := by rfl
def stateRow7_3_7_4 : List State := ParentOwnership.parentRow1250
def patch7_3_7_4 : Patch := literalDomain.zip stateRow7_3_7_4
theorem patch_states7_3_7_4 : patch7_3_7_4.map Prod.snd = stateRow7_3_7_4 := by rfl
def stateRow7_3_7_5 : List State := ParentOwnership.parentRow0048
def patch7_3_7_5 : Patch := literalDomain.zip stateRow7_3_7_5
theorem patch_states7_3_7_5 : patch7_3_7_5.map Prod.snd = stateRow7_3_7_5 := by rfl
def stateRow7_3_7_6 : List State := ParentOwnership.parentRow1246
def patch7_3_7_6 : Patch := literalDomain.zip stateRow7_3_7_6
theorem patch_states7_3_7_6 : patch7_3_7_6.map Prod.snd = stateRow7_3_7_6 := by rfl
def stateRow7_3_7_11 : List State := ParentOwnership.parentRow1241
def patch7_3_7_11 : Patch := literalDomain.zip stateRow7_3_7_11
theorem patch_states7_3_7_11 : patch7_3_7_11.map Prod.snd = stateRow7_3_7_11 := by rfl
def final7_3_7 : List Patch := [patch7_3_7_0, patch7_3_7_1, patch7_3_7_2, patch7_3_7_3, patch7_3_7_4, patch7_3_7_5, patch7_3_7_6, patch7_3_7_11]
def stateRows7_3_7 : List (List State) := [stateRow7_3_7_0, stateRow7_3_7_1, stateRow7_3_7_2, stateRow7_3_7_3, stateRow7_3_7_4, stateRow7_3_7_5, stateRow7_3_7_6, stateRow7_3_7_11]
theorem stateRows_eq7_3_7 : stateRows7_3_7 = final7_3_7.map (List.map Prod.snd) := by
  simp only [stateRows7_3_7, final7_3_7, List.map_cons, List.map_nil, patch_states7_3_7_0, patch_states7_3_7_1, patch_states7_3_7_2, patch_states7_3_7_3, patch_states7_3_7_4, patch_states7_3_7_5, patch_states7_3_7_6, patch_states7_3_7_11]
theorem final_states7_3_7 : final7_3_7 = stateRows7_3_7.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
