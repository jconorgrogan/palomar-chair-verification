module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart093
public import SpectreFinite.ParentOwnershipFinitePart126
public import SpectreFinite.ParentOwnershipFinitePart127

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_0_2_0 : List State := ParentOwnership.parentRow2028
def patch7_0_2_0 : Patch := literalDomain.zip stateRow7_0_2_0
theorem patch_states7_0_2_0 : patch7_0_2_0.map Prod.snd = stateRow7_0_2_0 := by rfl
def stateRow7_0_2_1 : List State := ParentOwnership.parentRow2029
def patch7_0_2_1 : Patch := literalDomain.zip stateRow7_0_2_1
theorem patch_states7_0_2_1 : patch7_0_2_1.map Prod.snd = stateRow7_0_2_1 := by rfl
def stateRow7_0_2_2 : List State := ParentOwnership.parentRow2030
def patch7_0_2_2 : Patch := literalDomain.zip stateRow7_0_2_2
theorem patch_states7_0_2_2 : patch7_0_2_2.map Prod.snd = stateRow7_0_2_2 := by rfl
def stateRow7_0_2_3 : List State := ParentOwnership.parentRow2031
def patch7_0_2_3 : Patch := literalDomain.zip stateRow7_0_2_3
theorem patch_states7_0_2_3 : patch7_0_2_3.map Prod.snd = stateRow7_0_2_3 := by rfl
def stateRow7_0_2_4 : List State := ParentOwnership.parentRow2032
def patch7_0_2_4 : Patch := literalDomain.zip stateRow7_0_2_4
theorem patch_states7_0_2_4 : patch7_0_2_4.map Prod.snd = stateRow7_0_2_4 := by rfl
def stateRow7_0_2_5 : List State := ParentOwnership.parentRow2033
def patch7_0_2_5 : Patch := literalDomain.zip stateRow7_0_2_5
theorem patch_states7_0_2_5 : patch7_0_2_5.map Prod.snd = stateRow7_0_2_5 := by rfl
def stateRow7_0_2_6 : List State := ParentOwnership.parentRow2034
def patch7_0_2_6 : Patch := literalDomain.zip stateRow7_0_2_6
theorem patch_states7_0_2_6 : patch7_0_2_6.map Prod.snd = stateRow7_0_2_6 := by rfl
def stateRow7_0_2_8 : List State := ParentOwnership.parentRow1499
def patch7_0_2_8 : Patch := literalDomain.zip stateRow7_0_2_8
theorem patch_states7_0_2_8 : patch7_0_2_8.map Prod.snd = stateRow7_0_2_8 := by rfl
def stateRow7_0_2_10 : List State := ParentOwnership.parentRow1500
def patch7_0_2_10 : Patch := literalDomain.zip stateRow7_0_2_10
theorem patch_states7_0_2_10 : patch7_0_2_10.map Prod.snd = stateRow7_0_2_10 := by rfl
def stateRow7_0_2_11 : List State := ParentOwnership.parentRow1501
def patch7_0_2_11 : Patch := literalDomain.zip stateRow7_0_2_11
theorem patch_states7_0_2_11 : patch7_0_2_11.map Prod.snd = stateRow7_0_2_11 := by rfl
def final7_0_2 : List Patch := [patch7_0_2_0, patch7_0_2_1, patch7_0_2_2, patch7_0_2_3, patch7_0_2_4, patch7_0_2_5, patch7_0_2_6, patch7_0_2_8, patch7_0_2_10, patch7_0_2_11]
def stateRows7_0_2 : List (List State) := [stateRow7_0_2_0, stateRow7_0_2_1, stateRow7_0_2_2, stateRow7_0_2_3, stateRow7_0_2_4, stateRow7_0_2_5, stateRow7_0_2_6, stateRow7_0_2_8, stateRow7_0_2_10, stateRow7_0_2_11]
theorem stateRows_eq7_0_2 : stateRows7_0_2 = final7_0_2.map (List.map Prod.snd) := by
  simp only [stateRows7_0_2, final7_0_2, List.map_cons, List.map_nil, patch_states7_0_2_0, patch_states7_0_2_1, patch_states7_0_2_2, patch_states7_0_2_3, patch_states7_0_2_4, patch_states7_0_2_5, patch_states7_0_2_6, patch_states7_0_2_8, patch_states7_0_2_10, patch_states7_0_2_11]
theorem final_states7_0_2 : final7_0_2 = stateRows7_0_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
