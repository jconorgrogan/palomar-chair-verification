module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart024
public import SpectreFinite.ParentOwnershipFinitePart092
public import SpectreFinite.ParentOwnershipFinitePart093
public import SpectreFinite.ParentOwnershipFinitePart094

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_2_5_0 : List State := ParentOwnership.parentRow1515
def patch8_2_5_0 : Patch := literalDomain.zip stateRow8_2_5_0
theorem patch_states8_2_5_0 : patch8_2_5_0.map Prod.snd = stateRow8_2_5_0 := by rfl
def stateRow8_2_5_1 : List State := ParentOwnership.parentRow0387
def patch8_2_5_1 : Patch := literalDomain.zip stateRow8_2_5_1
theorem patch_states8_2_5_1 : patch8_2_5_1.map Prod.snd = stateRow8_2_5_1 := by rfl
def stateRow8_2_5_2 : List State := ParentOwnership.parentRow0385
def patch8_2_5_2 : Patch := literalDomain.zip stateRow8_2_5_2
theorem patch_states8_2_5_2 : patch8_2_5_2.map Prod.snd = stateRow8_2_5_2 := by rfl
def stateRow8_2_5_3 : List State := ParentOwnership.parentRow1516
def patch8_2_5_3 : Patch := literalDomain.zip stateRow8_2_5_3
theorem patch_states8_2_5_3 : patch8_2_5_3.map Prod.snd = stateRow8_2_5_3 := by rfl
def stateRow8_2_5_4 : List State := ParentOwnership.parentRow1484
def patch8_2_5_4 : Patch := literalDomain.zip stateRow8_2_5_4
theorem patch_states8_2_5_4 : patch8_2_5_4.map Prod.snd = stateRow8_2_5_4 := by rfl
def stateRow8_2_5_5 : List State := ParentOwnership.parentRow1490
def patch8_2_5_5 : Patch := literalDomain.zip stateRow8_2_5_5
theorem patch_states8_2_5_5 : patch8_2_5_5.map Prod.snd = stateRow8_2_5_5 := by rfl
def stateRow8_2_5_6 : List State := ParentOwnership.parentRow1507
def patch8_2_5_6 : Patch := literalDomain.zip stateRow8_2_5_6
theorem patch_states8_2_5_6 : patch8_2_5_6.map Prod.snd = stateRow8_2_5_6 := by rfl
def stateRow8_2_5_7 : List State := ParentOwnership.parentRow1512
def patch8_2_5_7 : Patch := literalDomain.zip stateRow8_2_5_7
theorem patch_states8_2_5_7 : patch8_2_5_7.map Prod.snd = stateRow8_2_5_7 := by rfl
def stateRow8_2_5_8 : List State := ParentOwnership.parentRow1509
def patch8_2_5_8 : Patch := literalDomain.zip stateRow8_2_5_8
theorem patch_states8_2_5_8 : patch8_2_5_8.map Prod.snd = stateRow8_2_5_8 := by rfl
def stateRow8_2_5_9 : List State := ParentOwnership.parentRow1514
def patch8_2_5_9 : Patch := literalDomain.zip stateRow8_2_5_9
theorem patch_states8_2_5_9 : patch8_2_5_9.map Prod.snd = stateRow8_2_5_9 := by rfl
def final8_2_5 : List Patch := [patch8_2_5_0, patch8_2_5_1, patch8_2_5_2, patch8_2_5_3, patch8_2_5_4, patch8_2_5_5, patch8_2_5_6, patch8_2_5_7, patch8_2_5_8, patch8_2_5_9]
def stateRows8_2_5 : List (List State) := [stateRow8_2_5_0, stateRow8_2_5_1, stateRow8_2_5_2, stateRow8_2_5_3, stateRow8_2_5_4, stateRow8_2_5_5, stateRow8_2_5_6, stateRow8_2_5_7, stateRow8_2_5_8, stateRow8_2_5_9]
theorem stateRows_eq8_2_5 : stateRows8_2_5 = final8_2_5.map (List.map Prod.snd) := by
  simp only [stateRows8_2_5, final8_2_5, List.map_cons, List.map_nil, patch_states8_2_5_0, patch_states8_2_5_1, patch_states8_2_5_2, patch_states8_2_5_3, patch_states8_2_5_4, patch_states8_2_5_5, patch_states8_2_5_6, patch_states8_2_5_7, patch_states8_2_5_8, patch_states8_2_5_9]
theorem final_states8_2_5 : final8_2_5 = stateRows8_2_5.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
