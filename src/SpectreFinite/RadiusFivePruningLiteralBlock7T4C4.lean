module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart032
public import SpectreFinite.ParentOwnershipFinitePart060
public import SpectreFinite.ParentOwnershipFinitePart079
public import SpectreFinite.ParentOwnershipFinitePart105

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_4_4_1 : List State := ParentOwnership.parentRow0968
def patch7_4_4_1 : Patch := literalDomain.zip stateRow7_4_4_1
theorem patch_states7_4_4_1 : patch7_4_4_1.map Prod.snd = stateRow7_4_4_1 := by rfl
def stateRow7_4_4_2 : List State := ParentOwnership.parentRow1271
def patch7_4_4_2 : Patch := literalDomain.zip stateRow7_4_4_2
theorem patch_states7_4_4_2 : patch7_4_4_2.map Prod.snd = stateRow7_4_4_2 := by rfl
def stateRow7_4_4_3 : List State := ParentOwnership.parentRow1688
def patch7_4_4_3 : Patch := literalDomain.zip stateRow7_4_4_3
theorem patch_states7_4_4_3 : patch7_4_4_3.map Prod.snd = stateRow7_4_4_3 := by rfl
def stateRow7_4_4_4 : List State := ParentOwnership.parentRow1689
def patch7_4_4_4 : Patch := literalDomain.zip stateRow7_4_4_4
theorem patch_states7_4_4_4 : patch7_4_4_4.map Prod.snd = stateRow7_4_4_4 := by rfl
def stateRow7_4_4_5 : List State := ParentOwnership.parentRow0520
def patch7_4_4_5 : Patch := literalDomain.zip stateRow7_4_4_5
theorem patch_states7_4_4_5 : patch7_4_4_5.map Prod.snd = stateRow7_4_4_5 := by rfl
def stateRow7_4_4_8 : List State := ParentOwnership.parentRow1684
def patch7_4_4_8 : Patch := literalDomain.zip stateRow7_4_4_8
theorem patch_states7_4_4_8 : patch7_4_4_8.map Prod.snd = stateRow7_4_4_8 := by rfl
def stateRow7_4_4_10 : List State := ParentOwnership.parentRow1268
def patch7_4_4_10 : Patch := literalDomain.zip stateRow7_4_4_10
theorem patch_states7_4_4_10 : patch7_4_4_10.map Prod.snd = stateRow7_4_4_10 := by rfl
def final7_4_4 : List Patch := [patch7_4_4_1, patch7_4_4_2, patch7_4_4_3, patch7_4_4_4, patch7_4_4_5, patch7_4_4_8, patch7_4_4_10]
def stateRows7_4_4 : List (List State) := [stateRow7_4_4_1, stateRow7_4_4_2, stateRow7_4_4_3, stateRow7_4_4_4, stateRow7_4_4_5, stateRow7_4_4_8, stateRow7_4_4_10]
theorem stateRows_eq7_4_4 : stateRows7_4_4 = final7_4_4.map (List.map Prod.snd) := by
  simp only [stateRows7_4_4, final7_4_4, List.map_cons, List.map_nil, patch_states7_4_4_1, patch_states7_4_4_2, patch_states7_4_4_3, patch_states7_4_4_4, patch_states7_4_4_5, patch_states7_4_4_8, patch_states7_4_4_10]
theorem final_states7_4_4 : final7_4_4 = stateRows7_4_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
