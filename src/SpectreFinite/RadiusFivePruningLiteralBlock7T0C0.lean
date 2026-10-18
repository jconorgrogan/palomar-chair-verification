module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart048

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_0_0_1 : List State := ParentOwnership.parentRow0769
def patch7_0_0_1 : Patch := literalDomain.zip stateRow7_0_0_1
theorem patch_states7_0_0_1 : patch7_0_0_1.map Prod.snd = stateRow7_0_0_1 := by rfl
def stateRow7_0_0_2 : List State := ParentOwnership.parentRow0770
def patch7_0_0_2 : Patch := literalDomain.zip stateRow7_0_0_2
theorem patch_states7_0_0_2 : patch7_0_0_2.map Prod.snd = stateRow7_0_0_2 := by rfl
def stateRow7_0_0_3 : List State := ParentOwnership.parentRow0771
def patch7_0_0_3 : Patch := literalDomain.zip stateRow7_0_0_3
theorem patch_states7_0_0_3 : patch7_0_0_3.map Prod.snd = stateRow7_0_0_3 := by rfl
def stateRow7_0_0_4 : List State := ParentOwnership.parentRow0772
def patch7_0_0_4 : Patch := literalDomain.zip stateRow7_0_0_4
theorem patch_states7_0_0_4 : patch7_0_0_4.map Prod.snd = stateRow7_0_0_4 := by rfl
def stateRow7_0_0_5 : List State := ParentOwnership.parentRow0773
def patch7_0_0_5 : Patch := literalDomain.zip stateRow7_0_0_5
theorem patch_states7_0_0_5 : patch7_0_0_5.map Prod.snd = stateRow7_0_0_5 := by rfl
def stateRow7_0_0_6 : List State := ParentOwnership.parentRow0774
def patch7_0_0_6 : Patch := literalDomain.zip stateRow7_0_0_6
theorem patch_states7_0_0_6 : patch7_0_0_6.map Prod.snd = stateRow7_0_0_6 := by rfl
def stateRow7_0_0_7 : List State := ParentOwnership.parentRow0775
def patch7_0_0_7 : Patch := literalDomain.zip stateRow7_0_0_7
theorem patch_states7_0_0_7 : patch7_0_0_7.map Prod.snd = stateRow7_0_0_7 := by rfl
def stateRow7_0_0_8 : List State := ParentOwnership.parentRow0776
def patch7_0_0_8 : Patch := literalDomain.zip stateRow7_0_0_8
theorem patch_states7_0_0_8 : patch7_0_0_8.map Prod.snd = stateRow7_0_0_8 := by rfl
def stateRow7_0_0_11 : List State := ParentOwnership.parentRow0777
def patch7_0_0_11 : Patch := literalDomain.zip stateRow7_0_0_11
theorem patch_states7_0_0_11 : patch7_0_0_11.map Prod.snd = stateRow7_0_0_11 := by rfl
def final7_0_0 : List Patch := [patch7_0_0_1, patch7_0_0_2, patch7_0_0_3, patch7_0_0_4, patch7_0_0_5, patch7_0_0_6, patch7_0_0_7, patch7_0_0_8, patch7_0_0_11]
def stateRows7_0_0 : List (List State) := [stateRow7_0_0_1, stateRow7_0_0_2, stateRow7_0_0_3, stateRow7_0_0_4, stateRow7_0_0_5, stateRow7_0_0_6, stateRow7_0_0_7, stateRow7_0_0_8, stateRow7_0_0_11]
theorem stateRows_eq7_0_0 : stateRows7_0_0 = final7_0_0.map (List.map Prod.snd) := by
  simp only [stateRows7_0_0, final7_0_0, List.map_cons, List.map_nil, patch_states7_0_0_1, patch_states7_0_0_2, patch_states7_0_0_3, patch_states7_0_0_4, patch_states7_0_0_5, patch_states7_0_0_6, patch_states7_0_0_7, patch_states7_0_0_8, patch_states7_0_0_11]
theorem final_states7_0_0 : final7_0_0 = stateRows7_0_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
