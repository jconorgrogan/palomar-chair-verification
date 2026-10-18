module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart056
public import SpectreFinite.ParentOwnershipFinitePart057
public import SpectreFinite.ParentOwnershipFinitePart058
public import SpectreFinite.ParentOwnershipFinitePart059

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_1_0_1 : List State := ParentOwnership.parentRow0933
def patch7_1_0_1 : Patch := literalDomain.zip stateRow7_1_0_1
theorem patch_states7_1_0_1 : patch7_1_0_1.map Prod.snd = stateRow7_1_0_1 := by rfl
def stateRow7_1_0_2 : List State := ParentOwnership.parentRow0951
def patch7_1_0_2 : Patch := literalDomain.zip stateRow7_1_0_2
theorem patch_states7_1_0_2 : patch7_1_0_2.map Prod.snd = stateRow7_1_0_2 := by rfl
def stateRow7_1_0_3 : List State := ParentOwnership.parentRow0952
def patch7_1_0_3 : Patch := literalDomain.zip stateRow7_1_0_3
theorem patch_states7_1_0_3 : patch7_1_0_3.map Prod.snd = stateRow7_1_0_3 := by rfl
def stateRow7_1_0_4 : List State := ParentOwnership.parentRow0944
def patch7_1_0_4 : Patch := literalDomain.zip stateRow7_1_0_4
theorem patch_states7_1_0_4 : patch7_1_0_4.map Prod.snd = stateRow7_1_0_4 := by rfl
def stateRow7_1_0_5 : List State := ParentOwnership.parentRow0945
def patch7_1_0_5 : Patch := literalDomain.zip stateRow7_1_0_5
theorem patch_states7_1_0_5 : patch7_1_0_5.map Prod.snd = stateRow7_1_0_5 := by rfl
def stateRow7_1_0_6 : List State := ParentOwnership.parentRow0953
def patch7_1_0_6 : Patch := literalDomain.zip stateRow7_1_0_6
theorem patch_states7_1_0_6 : patch7_1_0_6.map Prod.snd = stateRow7_1_0_6 := by rfl
def stateRow7_1_0_7 : List State := ParentOwnership.parentRow0954
def patch7_1_0_7 : Patch := literalDomain.zip stateRow7_1_0_7
theorem patch_states7_1_0_7 : patch7_1_0_7.map Prod.snd = stateRow7_1_0_7 := by rfl
def stateRow7_1_0_8 : List State := ParentOwnership.parentRow0915
def patch7_1_0_8 : Patch := literalDomain.zip stateRow7_1_0_8
theorem patch_states7_1_0_8 : patch7_1_0_8.map Prod.snd = stateRow7_1_0_8 := by rfl
def stateRow7_1_0_11 : List State := ParentOwnership.parentRow0911
def patch7_1_0_11 : Patch := literalDomain.zip stateRow7_1_0_11
theorem patch_states7_1_0_11 : patch7_1_0_11.map Prod.snd = stateRow7_1_0_11 := by rfl
def final7_1_0 : List Patch := [patch7_1_0_1, patch7_1_0_2, patch7_1_0_3, patch7_1_0_4, patch7_1_0_5, patch7_1_0_6, patch7_1_0_7, patch7_1_0_8, patch7_1_0_11]
def stateRows7_1_0 : List (List State) := [stateRow7_1_0_1, stateRow7_1_0_2, stateRow7_1_0_3, stateRow7_1_0_4, stateRow7_1_0_5, stateRow7_1_0_6, stateRow7_1_0_7, stateRow7_1_0_8, stateRow7_1_0_11]
theorem stateRows_eq7_1_0 : stateRows7_1_0 = final7_1_0.map (List.map Prod.snd) := by
  simp only [stateRows7_1_0, final7_1_0, List.map_cons, List.map_nil, patch_states7_1_0_1, patch_states7_1_0_2, patch_states7_1_0_3, patch_states7_1_0_4, patch_states7_1_0_5, patch_states7_1_0_6, patch_states7_1_0_7, patch_states7_1_0_8, patch_states7_1_0_11]
theorem final_states7_1_0 : final7_1_0 = stateRows7_1_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
