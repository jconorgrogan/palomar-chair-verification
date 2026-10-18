module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart052
public import SpectreFinite.ParentOwnershipFinitePart053
public import SpectreFinite.ParentOwnershipFinitePart110
public import SpectreFinite.ParentOwnershipFinitePart112

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_1_4_1 : List State := ParentOwnership.parentRow0849
def patch7_1_4_1 : Patch := literalDomain.zip stateRow7_1_4_1
theorem patch_states7_1_4_1 : patch7_1_4_1.map Prod.snd = stateRow7_1_4_1 := by rfl
def stateRow7_1_4_2 : List State := ParentOwnership.parentRow0852
def patch7_1_4_2 : Patch := literalDomain.zip stateRow7_1_4_2
theorem patch_states7_1_4_2 : patch7_1_4_2.map Prod.snd = stateRow7_1_4_2 := by rfl
def stateRow7_1_4_3 : List State := ParentOwnership.parentRow0839
def patch7_1_4_3 : Patch := literalDomain.zip stateRow7_1_4_3
theorem patch_states7_1_4_3 : patch7_1_4_3.map Prod.snd = stateRow7_1_4_3 := by rfl
def stateRow7_1_4_4 : List State := ParentOwnership.parentRow0850
def patch7_1_4_4 : Patch := literalDomain.zip stateRow7_1_4_4
theorem patch_states7_1_4_4 : patch7_1_4_4.map Prod.snd = stateRow7_1_4_4 := by rfl
def stateRow7_1_4_5 : List State := ParentOwnership.parentRow0851
def patch7_1_4_5 : Patch := literalDomain.zip stateRow7_1_4_5
theorem patch_states7_1_4_5 : patch7_1_4_5.map Prod.snd = stateRow7_1_4_5 := by rfl
def stateRow7_1_4_8 : List State := ParentOwnership.parentRow1761
def patch7_1_4_8 : Patch := literalDomain.zip stateRow7_1_4_8
theorem patch_states7_1_4_8 : patch7_1_4_8.map Prod.snd = stateRow7_1_4_8 := by rfl
def stateRow7_1_4_10 : List State := ParentOwnership.parentRow1795
def patch7_1_4_10 : Patch := literalDomain.zip stateRow7_1_4_10
theorem patch_states7_1_4_10 : patch7_1_4_10.map Prod.snd = stateRow7_1_4_10 := by rfl
def final7_1_4 : List Patch := [patch7_1_4_1, patch7_1_4_2, patch7_1_4_3, patch7_1_4_4, patch7_1_4_5, patch7_1_4_8, patch7_1_4_10]
def stateRows7_1_4 : List (List State) := [stateRow7_1_4_1, stateRow7_1_4_2, stateRow7_1_4_3, stateRow7_1_4_4, stateRow7_1_4_5, stateRow7_1_4_8, stateRow7_1_4_10]
theorem stateRows_eq7_1_4 : stateRows7_1_4 = final7_1_4.map (List.map Prod.snd) := by
  simp only [stateRows7_1_4, final7_1_4, List.map_cons, List.map_nil, patch_states7_1_4_1, patch_states7_1_4_2, patch_states7_1_4_3, patch_states7_1_4_4, patch_states7_1_4_5, patch_states7_1_4_8, patch_states7_1_4_10]
theorem final_states7_1_4 : final7_1_4 = stateRows7_1_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
