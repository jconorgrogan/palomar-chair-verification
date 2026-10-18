module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart057
public import SpectreFinite.ParentOwnershipFinitePart058
public import SpectreFinite.ParentOwnershipFinitePart111
public import SpectreFinite.ParentOwnershipFinitePart112
public import SpectreFinite.ParentOwnershipFinitePart124

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_1_5_0 : List State := ParentOwnership.parentRow1787
def patch7_1_5_0 : Patch := literalDomain.zip stateRow7_1_5_0
theorem patch_states7_1_5_0 : patch7_1_5_0.map Prod.snd = stateRow7_1_5_0 := by rfl
def stateRow7_1_5_2 : List State := ParentOwnership.parentRow1794
def patch7_1_5_2 : Patch := literalDomain.zip stateRow7_1_5_2
theorem patch_states7_1_5_2 : patch7_1_5_2.map Prod.snd = stateRow7_1_5_2 := by rfl
def stateRow7_1_5_3 : List State := ParentOwnership.parentRow1796
def patch7_1_5_3 : Patch := literalDomain.zip stateRow7_1_5_3
theorem patch_states7_1_5_3 : patch7_1_5_3.map Prod.snd = stateRow7_1_5_3 := by rfl
def stateRow7_1_5_4 : List State := ParentOwnership.parentRow0921
def patch7_1_5_4 : Patch := literalDomain.zip stateRow7_1_5_4
theorem patch_states7_1_5_4 : patch7_1_5_4.map Prod.snd = stateRow7_1_5_4 := by rfl
def stateRow7_1_5_5 : List State := ParentOwnership.parentRow0931
def patch7_1_5_5 : Patch := literalDomain.zip stateRow7_1_5_5
theorem patch_states7_1_5_5 : patch7_1_5_5.map Prod.snd = stateRow7_1_5_5 := by rfl
def stateRow7_1_5_6 : List State := ParentOwnership.parentRow0928
def patch7_1_5_6 : Patch := literalDomain.zip stateRow7_1_5_6
theorem patch_states7_1_5_6 : patch7_1_5_6.map Prod.snd = stateRow7_1_5_6 := by rfl
def stateRow7_1_5_7 : List State := ParentOwnership.parentRow0932
def patch7_1_5_7 : Patch := literalDomain.zip stateRow7_1_5_7
theorem patch_states7_1_5_7 : patch7_1_5_7.map Prod.snd = stateRow7_1_5_7 := by rfl
def stateRow7_1_5_8 : List State := ParentOwnership.parentRow0939
def patch7_1_5_8 : Patch := literalDomain.zip stateRow7_1_5_8
theorem patch_states7_1_5_8 : patch7_1_5_8.map Prod.snd = stateRow7_1_5_8 := by rfl
def stateRow7_1_5_9 : List State := ParentOwnership.parentRow0943
def patch7_1_5_9 : Patch := literalDomain.zip stateRow7_1_5_9
theorem patch_states7_1_5_9 : patch7_1_5_9.map Prod.snd = stateRow7_1_5_9 := by rfl
def stateRow7_1_5_10 : List State := ParentOwnership.parentRow0940
def patch7_1_5_10 : Patch := literalDomain.zip stateRow7_1_5_10
theorem patch_states7_1_5_10 : patch7_1_5_10.map Prod.snd = stateRow7_1_5_10 := by rfl
def stateRow7_1_5_11 : List State := ParentOwnership.parentRow1987
def patch7_1_5_11 : Patch := literalDomain.zip stateRow7_1_5_11
theorem patch_states7_1_5_11 : patch7_1_5_11.map Prod.snd = stateRow7_1_5_11 := by rfl
def final7_1_5 : List Patch := [patch7_1_5_0, patch7_1_5_2, patch7_1_5_3, patch7_1_5_4, patch7_1_5_5, patch7_1_5_6, patch7_1_5_7, patch7_1_5_8, patch7_1_5_9, patch7_1_5_10, patch7_1_5_11]
def stateRows7_1_5 : List (List State) := [stateRow7_1_5_0, stateRow7_1_5_2, stateRow7_1_5_3, stateRow7_1_5_4, stateRow7_1_5_5, stateRow7_1_5_6, stateRow7_1_5_7, stateRow7_1_5_8, stateRow7_1_5_9, stateRow7_1_5_10, stateRow7_1_5_11]
theorem stateRows_eq7_1_5 : stateRows7_1_5 = final7_1_5.map (List.map Prod.snd) := by
  simp only [stateRows7_1_5, final7_1_5, List.map_cons, List.map_nil, patch_states7_1_5_0, patch_states7_1_5_2, patch_states7_1_5_3, patch_states7_1_5_4, patch_states7_1_5_5, patch_states7_1_5_6, patch_states7_1_5_7, patch_states7_1_5_8, patch_states7_1_5_9, patch_states7_1_5_10, patch_states7_1_5_11]
theorem final_states7_1_5 : final7_1_5 = stateRows7_1_5.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
