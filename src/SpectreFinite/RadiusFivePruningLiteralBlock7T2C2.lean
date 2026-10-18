module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart020
public import SpectreFinite.ParentOwnershipFinitePart036
public import SpectreFinite.ParentOwnershipFinitePart037
public import SpectreFinite.ParentOwnershipFinitePart087
public import SpectreFinite.ParentOwnershipFinitePart088

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_2_2_0 : List State := ParentOwnership.parentRow0590
def patch7_2_2_0 : Patch := literalDomain.zip stateRow7_2_2_0
theorem patch_states7_2_2_0 : patch7_2_2_0.map Prod.snd = stateRow7_2_2_0 := by rfl
def stateRow7_2_2_1 : List State := ParentOwnership.parentRow1393
def patch7_2_2_1 : Patch := literalDomain.zip stateRow7_2_2_1
theorem patch_states7_2_2_1 : patch7_2_2_1.map Prod.snd = stateRow7_2_2_1 := by rfl
def stateRow7_2_2_2 : List State := ParentOwnership.parentRow1403
def patch7_2_2_2 : Patch := literalDomain.zip stateRow7_2_2_2
theorem patch_states7_2_2_2 : patch7_2_2_2.map Prod.snd = stateRow7_2_2_2 := by rfl
def stateRow7_2_2_3 : List State := ParentOwnership.parentRow1402
def patch7_2_2_3 : Patch := literalDomain.zip stateRow7_2_2_3
theorem patch_states7_2_2_3 : patch7_2_2_3.map Prod.snd = stateRow7_2_2_3 := by rfl
def stateRow7_2_2_4 : List State := ParentOwnership.parentRow0325
def patch7_2_2_4 : Patch := literalDomain.zip stateRow7_2_2_4
theorem patch_states7_2_2_4 : patch7_2_2_4.map Prod.snd = stateRow7_2_2_4 := by rfl
def stateRow7_2_2_5 : List State := ParentOwnership.parentRow0592
def patch7_2_2_5 : Patch := literalDomain.zip stateRow7_2_2_5
theorem patch_states7_2_2_5 : patch7_2_2_5.map Prod.snd = stateRow7_2_2_5 := by rfl
def stateRow7_2_2_6 : List State := ParentOwnership.parentRow1404
def patch7_2_2_6 : Patch := literalDomain.zip stateRow7_2_2_6
theorem patch_states7_2_2_6 : patch7_2_2_6.map Prod.snd = stateRow7_2_2_6 := by rfl
def stateRow7_2_2_8 : List State := ParentOwnership.parentRow1409
def patch7_2_2_8 : Patch := literalDomain.zip stateRow7_2_2_8
theorem patch_states7_2_2_8 : patch7_2_2_8.map Prod.snd = stateRow7_2_2_8 := by rfl
def stateRow7_2_2_10 : List State := ParentOwnership.parentRow1410
def patch7_2_2_10 : Patch := literalDomain.zip stateRow7_2_2_10
theorem patch_states7_2_2_10 : patch7_2_2_10.map Prod.snd = stateRow7_2_2_10 := by rfl
def stateRow7_2_2_11 : List State := ParentOwnership.parentRow1412
def patch7_2_2_11 : Patch := literalDomain.zip stateRow7_2_2_11
theorem patch_states7_2_2_11 : patch7_2_2_11.map Prod.snd = stateRow7_2_2_11 := by rfl
def final7_2_2 : List Patch := [patch7_2_2_0, patch7_2_2_1, patch7_2_2_2, patch7_2_2_3, patch7_2_2_4, patch7_2_2_5, patch7_2_2_6, patch7_2_2_8, patch7_2_2_10, patch7_2_2_11]
def stateRows7_2_2 : List (List State) := [stateRow7_2_2_0, stateRow7_2_2_1, stateRow7_2_2_2, stateRow7_2_2_3, stateRow7_2_2_4, stateRow7_2_2_5, stateRow7_2_2_6, stateRow7_2_2_8, stateRow7_2_2_10, stateRow7_2_2_11]
theorem stateRows_eq7_2_2 : stateRows7_2_2 = final7_2_2.map (List.map Prod.snd) := by
  simp only [stateRows7_2_2, final7_2_2, List.map_cons, List.map_nil, patch_states7_2_2_0, patch_states7_2_2_1, patch_states7_2_2_2, patch_states7_2_2_3, patch_states7_2_2_4, patch_states7_2_2_5, patch_states7_2_2_6, patch_states7_2_2_8, patch_states7_2_2_10, patch_states7_2_2_11]
theorem final_states7_2_2 : final7_2_2 = stateRows7_2_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
