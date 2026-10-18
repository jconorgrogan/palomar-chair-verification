module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart063
public import SpectreFinite.ParentOwnershipFinitePart129
public import SpectreFinite.ParentOwnershipFinitePart130

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_5_0_1 : List State := ParentOwnership.parentRow1013
def patch1_5_0_1 : Patch := literalDomain.zip stateRow1_5_0_1
theorem patch_states1_5_0_1 : patch1_5_0_1.map Prod.snd = stateRow1_5_0_1 := by rfl
def stateRow1_5_0_2 : List State := ParentOwnership.parentRow2077
def patch1_5_0_2 : Patch := literalDomain.zip stateRow1_5_0_2
theorem patch_states1_5_0_2 : patch1_5_0_2.map Prod.snd = stateRow1_5_0_2 := by rfl
def stateRow1_5_0_3 : List State := ParentOwnership.parentRow2078
def patch1_5_0_3 : Patch := literalDomain.zip stateRow1_5_0_3
theorem patch_states1_5_0_3 : patch1_5_0_3.map Prod.snd = stateRow1_5_0_3 := by rfl
def stateRow1_5_0_5 : List State := ParentOwnership.parentRow2076
def patch1_5_0_5 : Patch := literalDomain.zip stateRow1_5_0_5
theorem patch_states1_5_0_5 : patch1_5_0_5.map Prod.snd = stateRow1_5_0_5 := by rfl
def stateRow1_5_0_6 : List State := ParentOwnership.parentRow2079
def patch1_5_0_6 : Patch := literalDomain.zip stateRow1_5_0_6
theorem patch_states1_5_0_6 : patch1_5_0_6.map Prod.snd = stateRow1_5_0_6 := by rfl
def stateRow1_5_0_7 : List State := ParentOwnership.parentRow2080
def patch1_5_0_7 : Patch := literalDomain.zip stateRow1_5_0_7
theorem patch_states1_5_0_7 : patch1_5_0_7.map Prod.snd = stateRow1_5_0_7 := by rfl
def stateRow1_5_0_8 : List State := ParentOwnership.parentRow2081
def patch1_5_0_8 : Patch := literalDomain.zip stateRow1_5_0_8
theorem patch_states1_5_0_8 : patch1_5_0_8.map Prod.snd = stateRow1_5_0_8 := by rfl
def stateRow1_5_0_9 : List State := ParentOwnership.parentRow2082
def patch1_5_0_9 : Patch := literalDomain.zip stateRow1_5_0_9
theorem patch_states1_5_0_9 : patch1_5_0_9.map Prod.snd = stateRow1_5_0_9 := by rfl
def stateRow1_5_0_10 : List State := ParentOwnership.parentRow1014
def patch1_5_0_10 : Patch := literalDomain.zip stateRow1_5_0_10
theorem patch_states1_5_0_10 : patch1_5_0_10.map Prod.snd = stateRow1_5_0_10 := by rfl
def stateRow1_5_0_11 : List State := ParentOwnership.parentRow1015
def patch1_5_0_11 : Patch := literalDomain.zip stateRow1_5_0_11
theorem patch_states1_5_0_11 : patch1_5_0_11.map Prod.snd = stateRow1_5_0_11 := by rfl
def final1_5_0 : List Patch := [patch1_5_0_1, patch1_5_0_2, patch1_5_0_3, patch1_5_0_5, patch1_5_0_6, patch1_5_0_7, patch1_5_0_8, patch1_5_0_9, patch1_5_0_10, patch1_5_0_11]
def stateRows1_5_0 : List (List State) := [stateRow1_5_0_1, stateRow1_5_0_2, stateRow1_5_0_3, stateRow1_5_0_5, stateRow1_5_0_6, stateRow1_5_0_7, stateRow1_5_0_8, stateRow1_5_0_9, stateRow1_5_0_10, stateRow1_5_0_11]
theorem stateRows_eq1_5_0 : stateRows1_5_0 = final1_5_0.map (List.map Prod.snd) := by
  simp only [stateRows1_5_0, final1_5_0, List.map_cons, List.map_nil, patch_states1_5_0_1, patch_states1_5_0_2, patch_states1_5_0_3, patch_states1_5_0_5, patch_states1_5_0_6, patch_states1_5_0_7, patch_states1_5_0_8, patch_states1_5_0_9, patch_states1_5_0_10, patch_states1_5_0_11]
theorem final_states1_5_0 : final1_5_0 = stateRows1_5_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
