module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart012
public import SpectreFinite.ParentOwnershipFinitePart013
public import SpectreFinite.ParentOwnershipFinitePart021
public import SpectreFinite.ParentOwnershipFinitePart022
public import SpectreFinite.ParentOwnershipFinitePart068

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_2_8_0 : List State := ParentOwnership.parentRow1092
def patch7_2_8_0 : Patch := literalDomain.zip stateRow7_2_8_0
theorem patch_states7_2_8_0 : patch7_2_8_0.map Prod.snd = stateRow7_2_8_0 := by rfl
def stateRow7_2_8_1 : List State := ParentOwnership.parentRow0347
def patch7_2_8_1 : Patch := literalDomain.zip stateRow7_2_8_1
theorem patch_states7_2_8_1 : patch7_2_8_1.map Prod.snd = stateRow7_2_8_1 := by rfl
def stateRow7_2_8_2 : List State := ParentOwnership.parentRow0353
def patch7_2_8_2 : Patch := literalDomain.zip stateRow7_2_8_2
theorem patch_states7_2_8_2 : patch7_2_8_2.map Prod.snd = stateRow7_2_8_2 := by rfl
def stateRow7_2_8_3 : List State := ParentOwnership.parentRow0346
def patch7_2_8_3 : Patch := literalDomain.zip stateRow7_2_8_3
theorem patch_states7_2_8_3 : patch7_2_8_3.map Prod.snd = stateRow7_2_8_3 := by rfl
def stateRow7_2_8_5 : List State := ParentOwnership.parentRow0216
def patch7_2_8_5 : Patch := literalDomain.zip stateRow7_2_8_5
theorem patch_states7_2_8_5 : patch7_2_8_5.map Prod.snd = stateRow7_2_8_5 := by rfl
def stateRow7_2_8_7 : List State := ParentOwnership.parentRow0202
def patch7_2_8_7 : Patch := literalDomain.zip stateRow7_2_8_7
theorem patch_states7_2_8_7 : patch7_2_8_7.map Prod.snd = stateRow7_2_8_7 := by rfl
def stateRow7_2_8_8 : List State := ParentOwnership.parentRow0217
def patch7_2_8_8 : Patch := literalDomain.zip stateRow7_2_8_8
theorem patch_states7_2_8_8 : patch7_2_8_8.map Prod.snd = stateRow7_2_8_8 := by rfl
def stateRow7_2_8_9 : List State := ParentOwnership.parentRow0218
def patch7_2_8_9 : Patch := literalDomain.zip stateRow7_2_8_9
theorem patch_states7_2_8_9 : patch7_2_8_9.map Prod.snd = stateRow7_2_8_9 := by rfl
def final7_2_8 : List Patch := [patch7_2_8_0, patch7_2_8_1, patch7_2_8_2, patch7_2_8_3, patch7_2_8_5, patch7_2_8_7, patch7_2_8_8, patch7_2_8_9]
def stateRows7_2_8 : List (List State) := [stateRow7_2_8_0, stateRow7_2_8_1, stateRow7_2_8_2, stateRow7_2_8_3, stateRow7_2_8_5, stateRow7_2_8_7, stateRow7_2_8_8, stateRow7_2_8_9]
theorem stateRows_eq7_2_8 : stateRows7_2_8 = final7_2_8.map (List.map Prod.snd) := by
  simp only [stateRows7_2_8, final7_2_8, List.map_cons, List.map_nil, patch_states7_2_8_0, patch_states7_2_8_1, patch_states7_2_8_2, patch_states7_2_8_3, patch_states7_2_8_5, patch_states7_2_8_7, patch_states7_2_8_8, patch_states7_2_8_9]
theorem final_states7_2_8 : final7_2_8 = stateRows7_2_8.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
