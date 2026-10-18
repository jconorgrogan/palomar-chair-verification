module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart002
public import SpectreFinite.ParentOwnershipFinitePart008
public import SpectreFinite.ParentOwnershipFinitePart012
public import SpectreFinite.ParentOwnershipFinitePart068
public import SpectreFinite.ParentOwnershipFinitePart078

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_3_2_0 : List State := ParentOwnership.parentRow0139
def patch1_3_2_0 : Patch := literalDomain.zip stateRow1_3_2_0
theorem patch_states1_3_2_0 : patch1_3_2_0.map Prod.snd = stateRow1_3_2_0 := by rfl
def stateRow1_3_2_1 : List State := ParentOwnership.parentRow0200
def patch1_3_2_1 : Patch := literalDomain.zip stateRow1_3_2_1
theorem patch_states1_3_2_1 : patch1_3_2_1.map Prod.snd = stateRow1_3_2_1 := by rfl
def stateRow1_3_2_2 : List State := ParentOwnership.parentRow0140
def patch1_3_2_2 : Patch := literalDomain.zip stateRow1_3_2_2
theorem patch_states1_3_2_2 : patch1_3_2_2.map Prod.snd = stateRow1_3_2_2 := by rfl
def stateRow1_3_2_3 : List State := ParentOwnership.parentRow1097
def patch1_3_2_3 : Patch := literalDomain.zip stateRow1_3_2_3
theorem patch_states1_3_2_3 : patch1_3_2_3.map Prod.snd = stateRow1_3_2_3 := by rfl
def stateRow1_3_2_4 : List State := ParentOwnership.parentRow0198
def patch1_3_2_4 : Patch := literalDomain.zip stateRow1_3_2_4
theorem patch_states1_3_2_4 : patch1_3_2_4.map Prod.snd = stateRow1_3_2_4 := by rfl
def stateRow1_3_2_6 : List State := ParentOwnership.parentRow1261
def patch1_3_2_6 : Patch := literalDomain.zip stateRow1_3_2_6
theorem patch_states1_3_2_6 : patch1_3_2_6.map Prod.snd = stateRow1_3_2_6 := by rfl
def stateRow1_3_2_7 : List State := ParentOwnership.parentRow1260
def patch1_3_2_7 : Patch := literalDomain.zip stateRow1_3_2_7
theorem patch_states1_3_2_7 : patch1_3_2_7.map Prod.snd = stateRow1_3_2_7 := by rfl
def stateRow1_3_2_8 : List State := ParentOwnership.parentRow0046
def patch1_3_2_8 : Patch := literalDomain.zip stateRow1_3_2_8
theorem patch_states1_3_2_8 : patch1_3_2_8.map Prod.snd = stateRow1_3_2_8 := by rfl
def stateRow1_3_2_9 : List State := ParentOwnership.parentRow1255
def patch1_3_2_9 : Patch := literalDomain.zip stateRow1_3_2_9
theorem patch_states1_3_2_9 : patch1_3_2_9.map Prod.snd = stateRow1_3_2_9 := by rfl
def stateRow1_3_2_11 : List State := ParentOwnership.parentRow0045
def patch1_3_2_11 : Patch := literalDomain.zip stateRow1_3_2_11
theorem patch_states1_3_2_11 : patch1_3_2_11.map Prod.snd = stateRow1_3_2_11 := by rfl
def final1_3_2 : List Patch := [patch1_3_2_0, patch1_3_2_1, patch1_3_2_2, patch1_3_2_3, patch1_3_2_4, patch1_3_2_6, patch1_3_2_7, patch1_3_2_8, patch1_3_2_9, patch1_3_2_11]
def stateRows1_3_2 : List (List State) := [stateRow1_3_2_0, stateRow1_3_2_1, stateRow1_3_2_2, stateRow1_3_2_3, stateRow1_3_2_4, stateRow1_3_2_6, stateRow1_3_2_7, stateRow1_3_2_8, stateRow1_3_2_9, stateRow1_3_2_11]
theorem stateRows_eq1_3_2 : stateRows1_3_2 = final1_3_2.map (List.map Prod.snd) := by
  simp only [stateRows1_3_2, final1_3_2, List.map_cons, List.map_nil, patch_states1_3_2_0, patch_states1_3_2_1, patch_states1_3_2_2, patch_states1_3_2_3, patch_states1_3_2_4, patch_states1_3_2_6, patch_states1_3_2_7, patch_states1_3_2_8, patch_states1_3_2_9, patch_states1_3_2_11]
theorem final_states1_3_2 : final1_3_2 = stateRows1_3_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
