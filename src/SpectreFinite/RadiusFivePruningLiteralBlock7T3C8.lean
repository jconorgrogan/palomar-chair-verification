module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart002
public import SpectreFinite.ParentOwnershipFinitePart003
public import SpectreFinite.ParentOwnershipFinitePart030
public import SpectreFinite.ParentOwnershipFinitePart076

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_3_8_0 : List State := ParentOwnership.parentRow1229
def patch7_3_8_0 : Patch := literalDomain.zip stateRow7_3_8_0
theorem patch_states7_3_8_0 : patch7_3_8_0.map Prod.snd = stateRow7_3_8_0 := by rfl
def stateRow7_3_8_1 : List State := ParentOwnership.parentRow1231
def patch7_3_8_1 : Patch := literalDomain.zip stateRow7_3_8_1
theorem patch_states7_3_8_1 : patch7_3_8_1.map Prod.snd = stateRow7_3_8_1 := by rfl
def stateRow7_3_8_2 : List State := ParentOwnership.parentRow0039
def patch7_3_8_2 : Patch := literalDomain.zip stateRow7_3_8_2
theorem patch_states7_3_8_2 : patch7_3_8_2.map Prod.snd = stateRow7_3_8_2 := by rfl
def stateRow7_3_8_3 : List State := ParentOwnership.parentRow1228
def patch7_3_8_3 : Patch := literalDomain.zip stateRow7_3_8_3
theorem patch_states7_3_8_3 : patch7_3_8_3.map Prod.snd = stateRow7_3_8_3 := by rfl
def stateRow7_3_8_5 : List State := ParentOwnership.parentRow0047
def patch7_3_8_5 : Patch := literalDomain.zip stateRow7_3_8_5
theorem patch_states7_3_8_5 : patch7_3_8_5.map Prod.snd = stateRow7_3_8_5 := by rfl
def stateRow7_3_8_7 : List State := ParentOwnership.parentRow0481
def patch7_3_8_7 : Patch := literalDomain.zip stateRow7_3_8_7
theorem patch_states7_3_8_7 : patch7_3_8_7.map Prod.snd = stateRow7_3_8_7 := by rfl
def stateRow7_3_8_8 : List State := ParentOwnership.parentRow0049
def patch7_3_8_8 : Patch := literalDomain.zip stateRow7_3_8_8
theorem patch_states7_3_8_8 : patch7_3_8_8.map Prod.snd = stateRow7_3_8_8 := by rfl
def stateRow7_3_8_9 : List State := ParentOwnership.parentRow0050
def patch7_3_8_9 : Patch := literalDomain.zip stateRow7_3_8_9
theorem patch_states7_3_8_9 : patch7_3_8_9.map Prod.snd = stateRow7_3_8_9 := by rfl
def final7_3_8 : List Patch := [patch7_3_8_0, patch7_3_8_1, patch7_3_8_2, patch7_3_8_3, patch7_3_8_5, patch7_3_8_7, patch7_3_8_8, patch7_3_8_9]
def stateRows7_3_8 : List (List State) := [stateRow7_3_8_0, stateRow7_3_8_1, stateRow7_3_8_2, stateRow7_3_8_3, stateRow7_3_8_5, stateRow7_3_8_7, stateRow7_3_8_8, stateRow7_3_8_9]
theorem stateRows_eq7_3_8 : stateRows7_3_8 = final7_3_8.map (List.map Prod.snd) := by
  simp only [stateRows7_3_8, final7_3_8, List.map_cons, List.map_nil, patch_states7_3_8_0, patch_states7_3_8_1, patch_states7_3_8_2, patch_states7_3_8_3, patch_states7_3_8_5, patch_states7_3_8_7, patch_states7_3_8_8, patch_states7_3_8_9]
theorem final_states7_3_8 : final7_3_8 = stateRows7_3_8.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
