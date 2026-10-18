module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart032
public import SpectreFinite.ParentOwnershipFinitePart040
public import SpectreFinite.ParentOwnershipFinitePart079
public import SpectreFinite.ParentOwnershipFinitePart105
public import SpectreFinite.ParentOwnershipFinitePart107

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_4_3_0 : List State := ParentOwnership.parentRow0649
def patch7_4_3_0 : Patch := literalDomain.zip stateRow7_4_3_0
theorem patch_states7_4_3_0 : patch7_4_3_0.map Prod.snd = stateRow7_4_3_0 := by rfl
def stateRow7_4_3_1 : List State := ParentOwnership.parentRow1722
def patch7_4_3_1 : Patch := literalDomain.zip stateRow7_4_3_1
theorem patch_states7_4_3_1 : patch7_4_3_1.map Prod.snd = stateRow7_4_3_1 := by rfl
def stateRow7_4_3_2 : List State := ParentOwnership.parentRow0650
def patch7_4_3_2 : Patch := literalDomain.zip stateRow7_4_3_2
theorem patch_states7_4_3_2 : patch7_4_3_2.map Prod.snd = stateRow7_4_3_2 := by rfl
def stateRow7_4_3_3 : List State := ParentOwnership.parentRow1723
def patch7_4_3_3 : Patch := literalDomain.zip stateRow7_4_3_3
theorem patch_states7_4_3_3 : patch7_4_3_3.map Prod.snd = stateRow7_4_3_3 := by rfl
def stateRow7_4_3_5 : List State := ParentOwnership.parentRow1272
def patch7_4_3_5 : Patch := literalDomain.zip stateRow7_4_3_5
theorem patch_states7_4_3_5 : patch7_4_3_5.map Prod.snd = stateRow7_4_3_5 := by rfl
def stateRow7_4_3_6 : List State := ParentOwnership.parentRow1270
def patch7_4_3_6 : Patch := literalDomain.zip stateRow7_4_3_6
theorem patch_states7_4_3_6 : patch7_4_3_6.map Prod.snd = stateRow7_4_3_6 := by rfl
def stateRow7_4_3_7 : List State := ParentOwnership.parentRow1686
def patch7_4_3_7 : Patch := literalDomain.zip stateRow7_4_3_7
theorem patch_states7_4_3_7 : patch7_4_3_7.map Prod.snd = stateRow7_4_3_7 := by rfl
def stateRow7_4_3_8 : List State := ParentOwnership.parentRow1687
def patch7_4_3_8 : Patch := literalDomain.zip stateRow7_4_3_8
theorem patch_states7_4_3_8 : patch7_4_3_8.map Prod.snd = stateRow7_4_3_8 := by rfl
def stateRow7_4_3_9 : List State := ParentOwnership.parentRow0521
def patch7_4_3_9 : Patch := literalDomain.zip stateRow7_4_3_9
theorem patch_states7_4_3_9 : patch7_4_3_9.map Prod.snd = stateRow7_4_3_9 := by rfl
def stateRow7_4_3_10 : List State := ParentOwnership.parentRow0519
def patch7_4_3_10 : Patch := literalDomain.zip stateRow7_4_3_10
theorem patch_states7_4_3_10 : patch7_4_3_10.map Prod.snd = stateRow7_4_3_10 := by rfl
def stateRow7_4_3_11 : List State := ParentOwnership.parentRow1269
def patch7_4_3_11 : Patch := literalDomain.zip stateRow7_4_3_11
theorem patch_states7_4_3_11 : patch7_4_3_11.map Prod.snd = stateRow7_4_3_11 := by rfl
def final7_4_3 : List Patch := [patch7_4_3_0, patch7_4_3_1, patch7_4_3_2, patch7_4_3_3, patch7_4_3_5, patch7_4_3_6, patch7_4_3_7, patch7_4_3_8, patch7_4_3_9, patch7_4_3_10, patch7_4_3_11]
def stateRows7_4_3 : List (List State) := [stateRow7_4_3_0, stateRow7_4_3_1, stateRow7_4_3_2, stateRow7_4_3_3, stateRow7_4_3_5, stateRow7_4_3_6, stateRow7_4_3_7, stateRow7_4_3_8, stateRow7_4_3_9, stateRow7_4_3_10, stateRow7_4_3_11]
theorem stateRows_eq7_4_3 : stateRows7_4_3 = final7_4_3.map (List.map Prod.snd) := by
  simp only [stateRows7_4_3, final7_4_3, List.map_cons, List.map_nil, patch_states7_4_3_0, patch_states7_4_3_1, patch_states7_4_3_2, patch_states7_4_3_3, patch_states7_4_3_5, patch_states7_4_3_6, patch_states7_4_3_7, patch_states7_4_3_8, patch_states7_4_3_9, patch_states7_4_3_10, patch_states7_4_3_11]
theorem final_states7_4_3 : final7_4_3 = stateRows7_4_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
