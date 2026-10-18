module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart012
public import SpectreFinite.ParentOwnershipFinitePart013
public import SpectreFinite.ParentOwnershipFinitePart021
public import SpectreFinite.ParentOwnershipFinitePart022

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_2_6_0 : List State := ParentOwnership.parentRow0209
def patch7_2_6_0 : Patch := literalDomain.zip stateRow7_2_6_0
theorem patch_states7_2_6_0 : patch7_2_6_0.map Prod.snd = stateRow7_2_6_0 := by rfl
def stateRow7_2_6_1 : List State := ParentOwnership.parentRow0196
def patch7_2_6_1 : Patch := literalDomain.zip stateRow7_2_6_1
theorem patch_states7_2_6_1 : patch7_2_6_1.map Prod.snd = stateRow7_2_6_1 := by rfl
def stateRow7_2_6_2 : List State := ParentOwnership.parentRow0208
def patch7_2_6_2 : Patch := literalDomain.zip stateRow7_2_6_2
theorem patch_states7_2_6_2 : patch7_2_6_2.map Prod.snd = stateRow7_2_6_2 := by rfl
def stateRow7_2_6_4 : List State := ParentOwnership.parentRow0192
def patch7_2_6_4 : Patch := literalDomain.zip stateRow7_2_6_4
theorem patch_states7_2_6_4 : patch7_2_6_4.map Prod.snd = stateRow7_2_6_4 := by rfl
def stateRow7_2_6_6 : List State := ParentOwnership.parentRow0203
def patch7_2_6_6 : Patch := literalDomain.zip stateRow7_2_6_6
theorem patch_states7_2_6_6 : patch7_2_6_6.map Prod.snd = stateRow7_2_6_6 := by rfl
def stateRow7_2_6_7 : List State := ParentOwnership.parentRow0205
def patch7_2_6_7 : Patch := literalDomain.zip stateRow7_2_6_7
theorem patch_states7_2_6_7 : patch7_2_6_7.map Prod.snd = stateRow7_2_6_7 := by rfl
def stateRow7_2_6_9 : List State := ParentOwnership.parentRow0348
def patch7_2_6_9 : Patch := literalDomain.zip stateRow7_2_6_9
theorem patch_states7_2_6_9 : patch7_2_6_9.map Prod.snd = stateRow7_2_6_9 := by rfl
def stateRow7_2_6_10 : List State := ParentOwnership.parentRow0349
def patch7_2_6_10 : Patch := literalDomain.zip stateRow7_2_6_10
theorem patch_states7_2_6_10 : patch7_2_6_10.map Prod.snd = stateRow7_2_6_10 := by rfl
def stateRow7_2_6_11 : List State := ParentOwnership.parentRow0354
def patch7_2_6_11 : Patch := literalDomain.zip stateRow7_2_6_11
theorem patch_states7_2_6_11 : patch7_2_6_11.map Prod.snd = stateRow7_2_6_11 := by rfl
def final7_2_6 : List Patch := [patch7_2_6_0, patch7_2_6_1, patch7_2_6_2, patch7_2_6_4, patch7_2_6_6, patch7_2_6_7, patch7_2_6_9, patch7_2_6_10, patch7_2_6_11]
def stateRows7_2_6 : List (List State) := [stateRow7_2_6_0, stateRow7_2_6_1, stateRow7_2_6_2, stateRow7_2_6_4, stateRow7_2_6_6, stateRow7_2_6_7, stateRow7_2_6_9, stateRow7_2_6_10, stateRow7_2_6_11]
theorem stateRows_eq7_2_6 : stateRows7_2_6 = final7_2_6.map (List.map Prod.snd) := by
  simp only [stateRows7_2_6, final7_2_6, List.map_cons, List.map_nil, patch_states7_2_6_0, patch_states7_2_6_1, patch_states7_2_6_2, patch_states7_2_6_4, patch_states7_2_6_6, patch_states7_2_6_7, patch_states7_2_6_9, patch_states7_2_6_10, patch_states7_2_6_11]
theorem final_states7_2_6 : final7_2_6 = stateRows7_2_6.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
