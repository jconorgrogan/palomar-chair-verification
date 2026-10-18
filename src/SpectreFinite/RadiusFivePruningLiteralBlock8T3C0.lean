module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart001
public import SpectreFinite.ParentOwnershipFinitePart029
public import SpectreFinite.ParentOwnershipFinitePart075
public import SpectreFinite.ParentOwnershipFinitePart076
public import SpectreFinite.ParentOwnershipFinitePart077

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_3_0_1 : List State := ParentOwnership.parentRow1213
def patch8_3_0_1 : Patch := literalDomain.zip stateRow8_3_0_1
theorem patch_states8_3_0_1 : patch8_3_0_1.map Prod.snd = stateRow8_3_0_1 := by rfl
def stateRow8_3_0_3 : List State := ParentOwnership.parentRow1212
def patch8_3_0_3 : Patch := literalDomain.zip stateRow8_3_0_3
theorem patch_states8_3_0_3 : patch8_3_0_3.map Prod.snd = stateRow8_3_0_3 := by rfl
def stateRow8_3_0_4 : List State := ParentOwnership.parentRow1214
def patch8_3_0_4 : Patch := literalDomain.zip stateRow8_3_0_4
theorem patch_states8_3_0_4 : patch8_3_0_4.map Prod.snd = stateRow8_3_0_4 := by rfl
def stateRow8_3_0_5 : List State := ParentOwnership.parentRow1235
def patch8_3_0_5 : Patch := literalDomain.zip stateRow8_3_0_5
theorem patch_states8_3_0_5 : patch8_3_0_5.map Prod.snd = stateRow8_3_0_5 := by rfl
def stateRow8_3_0_6 : List State := ParentOwnership.parentRow1237
def patch8_3_0_6 : Patch := literalDomain.zip stateRow8_3_0_6
theorem patch_states8_3_0_6 : patch8_3_0_6.map Prod.snd = stateRow8_3_0_6 := by rfl
def stateRow8_3_0_7 : List State := ParentOwnership.parentRow1216
def patch8_3_0_7 : Patch := literalDomain.zip stateRow8_3_0_7
theorem patch_states8_3_0_7 : patch8_3_0_7.map Prod.snd = stateRow8_3_0_7 := by rfl
def stateRow8_3_0_8 : List State := ParentOwnership.parentRow0025
def patch8_3_0_8 : Patch := literalDomain.zip stateRow8_3_0_8
theorem patch_states8_3_0_8 : patch8_3_0_8.map Prod.snd = stateRow8_3_0_8 := by rfl
def stateRow8_3_0_9 : List State := ParentOwnership.parentRow0473
def patch8_3_0_9 : Patch := literalDomain.zip stateRow8_3_0_9
theorem patch_states8_3_0_9 : patch8_3_0_9.map Prod.snd = stateRow8_3_0_9 := by rfl
def stateRow8_3_0_10 : List State := ParentOwnership.parentRow1236
def patch8_3_0_10 : Patch := literalDomain.zip stateRow8_3_0_10
theorem patch_states8_3_0_10 : patch8_3_0_10.map Prod.snd = stateRow8_3_0_10 := by rfl
def stateRow8_3_0_11 : List State := ParentOwnership.parentRow0477
def patch8_3_0_11 : Patch := literalDomain.zip stateRow8_3_0_11
theorem patch_states8_3_0_11 : patch8_3_0_11.map Prod.snd = stateRow8_3_0_11 := by rfl
def final8_3_0 : List Patch := [patch8_3_0_1, patch8_3_0_3, patch8_3_0_4, patch8_3_0_5, patch8_3_0_6, patch8_3_0_7, patch8_3_0_8, patch8_3_0_9, patch8_3_0_10, patch8_3_0_11]
def stateRows8_3_0 : List (List State) := [stateRow8_3_0_1, stateRow8_3_0_3, stateRow8_3_0_4, stateRow8_3_0_5, stateRow8_3_0_6, stateRow8_3_0_7, stateRow8_3_0_8, stateRow8_3_0_9, stateRow8_3_0_10, stateRow8_3_0_11]
theorem stateRows_eq8_3_0 : stateRows8_3_0 = final8_3_0.map (List.map Prod.snd) := by
  simp only [stateRows8_3_0, final8_3_0, List.map_cons, List.map_nil, patch_states8_3_0_1, patch_states8_3_0_3, patch_states8_3_0_4, patch_states8_3_0_5, patch_states8_3_0_6, patch_states8_3_0_7, patch_states8_3_0_8, patch_states8_3_0_9, patch_states8_3_0_10, patch_states8_3_0_11]
theorem final_states8_3_0 : final8_3_0 = stateRows8_3_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
