module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart012
public import SpectreFinite.ParentOwnershipFinitePart013
public import SpectreFinite.ParentOwnershipFinitePart022

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_2_7_0 : List State := ParentOwnership.parentRow0355
def patch7_2_7_0 : Patch := literalDomain.zip stateRow7_2_7_0
theorem patch_states7_2_7_0 : patch7_2_7_0.map Prod.snd = stateRow7_2_7_0 := by rfl
def stateRow7_2_7_1 : List State := ParentOwnership.parentRow0212
def patch7_2_7_1 : Patch := literalDomain.zip stateRow7_2_7_1
theorem patch_states7_2_7_1 : patch7_2_7_1.map Prod.snd = stateRow7_2_7_1 := by rfl
def stateRow7_2_7_2 : List State := ParentOwnership.parentRow0213
def patch7_2_7_2 : Patch := literalDomain.zip stateRow7_2_7_2
theorem patch_states7_2_7_2 : patch7_2_7_2.map Prod.snd = stateRow7_2_7_2 := by rfl
def stateRow7_2_7_3 : List State := ParentOwnership.parentRow0194
def patch7_2_7_3 : Patch := literalDomain.zip stateRow7_2_7_3
theorem patch_states7_2_7_3 : patch7_2_7_3.map Prod.snd = stateRow7_2_7_3 := by rfl
def stateRow7_2_7_4 : List State := ParentOwnership.parentRow0195
def patch7_2_7_4 : Patch := literalDomain.zip stateRow7_2_7_4
theorem patch_states7_2_7_4 : patch7_2_7_4.map Prod.snd = stateRow7_2_7_4 := by rfl
def stateRow7_2_7_5 : List State := ParentOwnership.parentRow0215
def patch7_2_7_5 : Patch := literalDomain.zip stateRow7_2_7_5
theorem patch_states7_2_7_5 : patch7_2_7_5.map Prod.snd = stateRow7_2_7_5 := by rfl
def stateRow7_2_7_6 : List State := ParentOwnership.parentRow0210
def patch7_2_7_6 : Patch := literalDomain.zip stateRow7_2_7_6
theorem patch_states7_2_7_6 : patch7_2_7_6.map Prod.snd = stateRow7_2_7_6 := by rfl
def stateRow7_2_7_11 : List State := ParentOwnership.parentRow0204
def patch7_2_7_11 : Patch := literalDomain.zip stateRow7_2_7_11
theorem patch_states7_2_7_11 : patch7_2_7_11.map Prod.snd = stateRow7_2_7_11 := by rfl
def final7_2_7 : List Patch := [patch7_2_7_0, patch7_2_7_1, patch7_2_7_2, patch7_2_7_3, patch7_2_7_4, patch7_2_7_5, patch7_2_7_6, patch7_2_7_11]
def stateRows7_2_7 : List (List State) := [stateRow7_2_7_0, stateRow7_2_7_1, stateRow7_2_7_2, stateRow7_2_7_3, stateRow7_2_7_4, stateRow7_2_7_5, stateRow7_2_7_6, stateRow7_2_7_11]
theorem stateRows_eq7_2_7 : stateRows7_2_7 = final7_2_7.map (List.map Prod.snd) := by
  simp only [stateRows7_2_7, final7_2_7, List.map_cons, List.map_nil, patch_states7_2_7_0, patch_states7_2_7_1, patch_states7_2_7_2, patch_states7_2_7_3, patch_states7_2_7_4, patch_states7_2_7_5, patch_states7_2_7_6, patch_states7_2_7_11]
theorem final_states7_2_7 : final7_2_7 = stateRows7_2_7.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
