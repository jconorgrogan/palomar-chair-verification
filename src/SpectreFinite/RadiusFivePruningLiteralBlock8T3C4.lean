module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart028
public import SpectreFinite.ParentOwnershipFinitePart029
public import SpectreFinite.ParentOwnershipFinitePart100
public import SpectreFinite.ParentOwnershipFinitePart102

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_3_4_0 : List State := ParentOwnership.parentRow0460
def patch8_3_4_0 : Patch := literalDomain.zip stateRow8_3_4_0
theorem patch_states8_3_4_0 : patch8_3_4_0.map Prod.snd = stateRow8_3_4_0 := by rfl
def stateRow8_3_4_1 : List State := ParentOwnership.parentRow0474
def patch8_3_4_1 : Patch := literalDomain.zip stateRow8_3_4_1
theorem patch_states8_3_4_1 : patch8_3_4_1.map Prod.snd = stateRow8_3_4_1 := by rfl
def stateRow8_3_4_2 : List State := ParentOwnership.parentRow0466
def patch8_3_4_2 : Patch := literalDomain.zip stateRow8_3_4_2
theorem patch_states8_3_4_2 : patch8_3_4_2.map Prod.snd = stateRow8_3_4_2 := by rfl
def stateRow8_3_4_3 : List State := ParentOwnership.parentRow0475
def patch8_3_4_3 : Patch := literalDomain.zip stateRow8_3_4_3
theorem patch_states8_3_4_3 : patch8_3_4_3.map Prod.snd = stateRow8_3_4_3 := by rfl
def stateRow8_3_4_4 : List State := ParentOwnership.parentRow0467
def patch8_3_4_4 : Patch := literalDomain.zip stateRow8_3_4_4
theorem patch_states8_3_4_4 : patch8_3_4_4.map Prod.snd = stateRow8_3_4_4 := by rfl
def stateRow8_3_4_5 : List State := ParentOwnership.parentRow1635
def patch8_3_4_5 : Patch := literalDomain.zip stateRow8_3_4_5
theorem patch_states8_3_4_5 : patch8_3_4_5.map Prod.snd = stateRow8_3_4_5 := by rfl
def stateRow8_3_4_8 : List State := ParentOwnership.parentRow1604
def patch8_3_4_8 : Patch := literalDomain.zip stateRow8_3_4_8
theorem patch_states8_3_4_8 : patch8_3_4_8.map Prod.snd = stateRow8_3_4_8 := by rfl
def stateRow8_3_4_9 : List State := ParentOwnership.parentRow1638
def patch8_3_4_9 : Patch := literalDomain.zip stateRow8_3_4_9
theorem patch_states8_3_4_9 : patch8_3_4_9.map Prod.snd = stateRow8_3_4_9 := by rfl
def stateRow8_3_4_10 : List State := ParentOwnership.parentRow0461
def patch8_3_4_10 : Patch := literalDomain.zip stateRow8_3_4_10
theorem patch_states8_3_4_10 : patch8_3_4_10.map Prod.snd = stateRow8_3_4_10 := by rfl
def stateRow8_3_4_11 : List State := ParentOwnership.parentRow1641
def patch8_3_4_11 : Patch := literalDomain.zip stateRow8_3_4_11
theorem patch_states8_3_4_11 : patch8_3_4_11.map Prod.snd = stateRow8_3_4_11 := by rfl
def final8_3_4 : List Patch := [patch8_3_4_0, patch8_3_4_1, patch8_3_4_2, patch8_3_4_3, patch8_3_4_4, patch8_3_4_5, patch8_3_4_8, patch8_3_4_9, patch8_3_4_10, patch8_3_4_11]
def stateRows8_3_4 : List (List State) := [stateRow8_3_4_0, stateRow8_3_4_1, stateRow8_3_4_2, stateRow8_3_4_3, stateRow8_3_4_4, stateRow8_3_4_5, stateRow8_3_4_8, stateRow8_3_4_9, stateRow8_3_4_10, stateRow8_3_4_11]
theorem stateRows_eq8_3_4 : stateRows8_3_4 = final8_3_4.map (List.map Prod.snd) := by
  simp only [stateRows8_3_4, final8_3_4, List.map_cons, List.map_nil, patch_states8_3_4_0, patch_states8_3_4_1, patch_states8_3_4_2, patch_states8_3_4_3, patch_states8_3_4_4, patch_states8_3_4_5, patch_states8_3_4_8, patch_states8_3_4_9, patch_states8_3_4_10, patch_states8_3_4_11]
theorem final_states8_3_4 : final8_3_4 = stateRows8_3_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
