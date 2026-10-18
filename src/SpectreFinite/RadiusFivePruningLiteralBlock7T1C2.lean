module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart037
public import SpectreFinite.ParentOwnershipFinitePart059
public import SpectreFinite.ParentOwnershipFinitePart097
public import SpectreFinite.ParentOwnershipFinitePart098

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_1_2_0 : List State := ParentOwnership.parentRow0600
def patch7_1_2_0 : Patch := literalDomain.zip stateRow7_1_2_0
theorem patch_states7_1_2_0 : patch7_1_2_0.map Prod.snd = stateRow7_1_2_0 := by rfl
def stateRow7_1_2_1 : List State := ParentOwnership.parentRow0602
def patch7_1_2_1 : Patch := literalDomain.zip stateRow7_1_2_1
theorem patch_states7_1_2_1 : patch7_1_2_1.map Prod.snd = stateRow7_1_2_1 := by rfl
def stateRow7_1_2_2 : List State := ParentOwnership.parentRow0604
def patch7_1_2_2 : Patch := literalDomain.zip stateRow7_1_2_2
theorem patch_states7_1_2_2 : patch7_1_2_2.map Prod.snd = stateRow7_1_2_2 := by rfl
def stateRow7_1_2_3 : List State := ParentOwnership.parentRow1569
def patch7_1_2_3 : Patch := literalDomain.zip stateRow7_1_2_3
theorem patch_states7_1_2_3 : patch7_1_2_3.map Prod.snd = stateRow7_1_2_3 := by rfl
def stateRow7_1_2_4 : List State := ParentOwnership.parentRow1562
def patch7_1_2_4 : Patch := literalDomain.zip stateRow7_1_2_4
theorem patch_states7_1_2_4 : patch7_1_2_4.map Prod.snd = stateRow7_1_2_4 := by rfl
def stateRow7_1_2_5 : List State := ParentOwnership.parentRow1565
def patch7_1_2_5 : Patch := literalDomain.zip stateRow7_1_2_5
theorem patch_states7_1_2_5 : patch7_1_2_5.map Prod.snd = stateRow7_1_2_5 := by rfl
def stateRow7_1_2_6 : List State := ParentOwnership.parentRow1568
def patch7_1_2_6 : Patch := literalDomain.zip stateRow7_1_2_6
theorem patch_states7_1_2_6 : patch7_1_2_6.map Prod.snd = stateRow7_1_2_6 := by rfl
def stateRow7_1_2_8 : List State := ParentOwnership.parentRow0948
def patch7_1_2_8 : Patch := literalDomain.zip stateRow7_1_2_8
theorem patch_states7_1_2_8 : patch7_1_2_8.map Prod.snd = stateRow7_1_2_8 := by rfl
def stateRow7_1_2_10 : List State := ParentOwnership.parentRow0946
def patch7_1_2_10 : Patch := literalDomain.zip stateRow7_1_2_10
theorem patch_states7_1_2_10 : patch7_1_2_10.map Prod.snd = stateRow7_1_2_10 := by rfl
def stateRow7_1_2_11 : List State := ParentOwnership.parentRow0947
def patch7_1_2_11 : Patch := literalDomain.zip stateRow7_1_2_11
theorem patch_states7_1_2_11 : patch7_1_2_11.map Prod.snd = stateRow7_1_2_11 := by rfl
def final7_1_2 : List Patch := [patch7_1_2_0, patch7_1_2_1, patch7_1_2_2, patch7_1_2_3, patch7_1_2_4, patch7_1_2_5, patch7_1_2_6, patch7_1_2_8, patch7_1_2_10, patch7_1_2_11]
def stateRows7_1_2 : List (List State) := [stateRow7_1_2_0, stateRow7_1_2_1, stateRow7_1_2_2, stateRow7_1_2_3, stateRow7_1_2_4, stateRow7_1_2_5, stateRow7_1_2_6, stateRow7_1_2_8, stateRow7_1_2_10, stateRow7_1_2_11]
theorem stateRows_eq7_1_2 : stateRows7_1_2 = final7_1_2.map (List.map Prod.snd) := by
  simp only [stateRows7_1_2, final7_1_2, List.map_cons, List.map_nil, patch_states7_1_2_0, patch_states7_1_2_1, patch_states7_1_2_2, patch_states7_1_2_3, patch_states7_1_2_4, patch_states7_1_2_5, patch_states7_1_2_6, patch_states7_1_2_8, patch_states7_1_2_10, patch_states7_1_2_11]
theorem final_states7_1_2 : final7_1_2 = stateRows7_1_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
