module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart020
public import SpectreFinite.ParentOwnershipFinitePart024
public import SpectreFinite.ParentOwnershipFinitePart036
public import SpectreFinite.ParentOwnershipFinitePart092
public import SpectreFinite.ParentOwnershipFinitePart093

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_2_2_0 : List State := ParentOwnership.parentRow0390
def patch8_2_2_0 : Patch := literalDomain.zip stateRow8_2_2_0
theorem patch_states8_2_2_0 : patch8_2_2_0.map Prod.snd = stateRow8_2_2_0 := by rfl
def stateRow8_2_2_2 : List State := ParentOwnership.parentRow0321
def patch8_2_2_2 : Patch := literalDomain.zip stateRow8_2_2_2
theorem patch_states8_2_2_2 : patch8_2_2_2.map Prod.snd = stateRow8_2_2_2 := by rfl
def stateRow8_2_2_3 : List State := ParentOwnership.parentRow0589
def patch8_2_2_3 : Patch := literalDomain.zip stateRow8_2_2_3
theorem patch_states8_2_2_3 : patch8_2_2_3.map Prod.snd = stateRow8_2_2_3 := by rfl
def stateRow8_2_2_4 : List State := ParentOwnership.parentRow0324
def patch8_2_2_4 : Patch := literalDomain.zip stateRow8_2_2_4
theorem patch_states8_2_2_4 : patch8_2_2_4.map Prod.snd = stateRow8_2_2_4 := by rfl
def stateRow8_2_2_5 : List State := ParentOwnership.parentRow0591
def patch8_2_2_5 : Patch := literalDomain.zip stateRow8_2_2_5
theorem patch_states8_2_2_5 : patch8_2_2_5.map Prod.snd = stateRow8_2_2_5 := by rfl
def stateRow8_2_2_6 : List State := ParentOwnership.parentRow1488
def patch8_2_2_6 : Patch := literalDomain.zip stateRow8_2_2_6
theorem patch_states8_2_2_6 : patch8_2_2_6.map Prod.snd = stateRow8_2_2_6 := by rfl
def stateRow8_2_2_7 : List State := ParentOwnership.parentRow1486
def patch8_2_2_7 : Patch := literalDomain.zip stateRow8_2_2_7
theorem patch_states8_2_2_7 : patch8_2_2_7.map Prod.snd = stateRow8_2_2_7 := by rfl
def stateRow8_2_2_8 : List State := ParentOwnership.parentRow1487
def patch8_2_2_8 : Patch := literalDomain.zip stateRow8_2_2_8
theorem patch_states8_2_2_8 : patch8_2_2_8.map Prod.snd = stateRow8_2_2_8 := by rfl
def stateRow8_2_2_9 : List State := ParentOwnership.parentRow1492
def patch8_2_2_9 : Patch := literalDomain.zip stateRow8_2_2_9
theorem patch_states8_2_2_9 : patch8_2_2_9.map Prod.snd = stateRow8_2_2_9 := by rfl
def stateRow8_2_2_10 : List State := ParentOwnership.parentRow1485
def patch8_2_2_10 : Patch := literalDomain.zip stateRow8_2_2_10
theorem patch_states8_2_2_10 : patch8_2_2_10.map Prod.snd = stateRow8_2_2_10 := by rfl
def stateRow8_2_2_11 : List State := ParentOwnership.parentRow1491
def patch8_2_2_11 : Patch := literalDomain.zip stateRow8_2_2_11
theorem patch_states8_2_2_11 : patch8_2_2_11.map Prod.snd = stateRow8_2_2_11 := by rfl
def final8_2_2 : List Patch := [patch8_2_2_0, patch8_2_2_2, patch8_2_2_3, patch8_2_2_4, patch8_2_2_5, patch8_2_2_6, patch8_2_2_7, patch8_2_2_8, patch8_2_2_9, patch8_2_2_10, patch8_2_2_11]
def stateRows8_2_2 : List (List State) := [stateRow8_2_2_0, stateRow8_2_2_2, stateRow8_2_2_3, stateRow8_2_2_4, stateRow8_2_2_5, stateRow8_2_2_6, stateRow8_2_2_7, stateRow8_2_2_8, stateRow8_2_2_9, stateRow8_2_2_10, stateRow8_2_2_11]
theorem stateRows_eq8_2_2 : stateRows8_2_2 = final8_2_2.map (List.map Prod.snd) := by
  simp only [stateRows8_2_2, final8_2_2, List.map_cons, List.map_nil, patch_states8_2_2_0, patch_states8_2_2_2, patch_states8_2_2_3, patch_states8_2_2_4, patch_states8_2_2_5, patch_states8_2_2_6, patch_states8_2_2_7, patch_states8_2_2_8, patch_states8_2_2_9, patch_states8_2_2_10, patch_states8_2_2_11]
theorem final_states8_2_2 : final8_2_2 = stateRows8_2_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
