module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart045
public import SpectreFinite.ParentOwnershipFinitePart095
public import SpectreFinite.ParentOwnershipFinitePart097
public import SpectreFinite.ParentOwnershipFinitePart098
public import SpectreFinite.ParentOwnershipFinitePart121
public import SpectreFinite.ParentOwnershipFinitePart122

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_1_3_0 : List State := ParentOwnership.parentRow0731
def patch8_1_3_0 : Patch := literalDomain.zip stateRow8_1_3_0
theorem patch_states8_1_3_0 : patch8_1_3_0.map Prod.snd = stateRow8_1_3_0 := by rfl
def stateRow8_1_3_1 : List State := ParentOwnership.parentRow0732
def patch8_1_3_1 : Patch := literalDomain.zip stateRow8_1_3_1
theorem patch_states8_1_3_1 : patch8_1_3_1.map Prod.snd = stateRow8_1_3_1 := by rfl
def stateRow8_1_3_3 : List State := ParentOwnership.parentRow1949
def patch8_1_3_3 : Patch := literalDomain.zip stateRow8_1_3_3
theorem patch_states8_1_3_3 : patch8_1_3_3.map Prod.snd = stateRow8_1_3_3 := by rfl
def stateRow8_1_3_4 : List State := ParentOwnership.parentRow1950
def patch8_1_3_4 : Patch := literalDomain.zip stateRow8_1_3_4
theorem patch_states8_1_3_4 : patch8_1_3_4.map Prod.snd = stateRow8_1_3_4 := by rfl
def stateRow8_1_3_5 : List State := ParentOwnership.parentRow1951
def patch8_1_3_5 : Patch := literalDomain.zip stateRow8_1_3_5
theorem patch_states8_1_3_5 : patch8_1_3_5.map Prod.snd = stateRow8_1_3_5 := by rfl
def stateRow8_1_3_6 : List State := ParentOwnership.parentRow1957
def patch8_1_3_6 : Patch := literalDomain.zip stateRow8_1_3_6
theorem patch_states8_1_3_6 : patch8_1_3_6.map Prod.snd = stateRow8_1_3_6 := by rfl
def stateRow8_1_3_7 : List State := ParentOwnership.parentRow1527
def patch8_1_3_7 : Patch := literalDomain.zip stateRow8_1_3_7
theorem patch_states8_1_3_7 : patch8_1_3_7.map Prod.snd = stateRow8_1_3_7 := by rfl
def stateRow8_1_3_8 : List State := ParentOwnership.parentRow1529
def patch8_1_3_8 : Patch := literalDomain.zip stateRow8_1_3_8
theorem patch_states8_1_3_8 : patch8_1_3_8.map Prod.snd = stateRow8_1_3_8 := by rfl
def stateRow8_1_3_9 : List State := ParentOwnership.parentRow1554
def patch8_1_3_9 : Patch := literalDomain.zip stateRow8_1_3_9
theorem patch_states8_1_3_9 : patch8_1_3_9.map Prod.snd = stateRow8_1_3_9 := by rfl
def stateRow8_1_3_10 : List State := ParentOwnership.parentRow1556
def patch8_1_3_10 : Patch := literalDomain.zip stateRow8_1_3_10
theorem patch_states8_1_3_10 : patch8_1_3_10.map Prod.snd = stateRow8_1_3_10 := by rfl
def stateRow8_1_3_11 : List State := ParentOwnership.parentRow1573
def patch8_1_3_11 : Patch := literalDomain.zip stateRow8_1_3_11
theorem patch_states8_1_3_11 : patch8_1_3_11.map Prod.snd = stateRow8_1_3_11 := by rfl
def final8_1_3 : List Patch := [patch8_1_3_0, patch8_1_3_1, patch8_1_3_3, patch8_1_3_4, patch8_1_3_5, patch8_1_3_6, patch8_1_3_7, patch8_1_3_8, patch8_1_3_9, patch8_1_3_10, patch8_1_3_11]
def stateRows8_1_3 : List (List State) := [stateRow8_1_3_0, stateRow8_1_3_1, stateRow8_1_3_3, stateRow8_1_3_4, stateRow8_1_3_5, stateRow8_1_3_6, stateRow8_1_3_7, stateRow8_1_3_8, stateRow8_1_3_9, stateRow8_1_3_10, stateRow8_1_3_11]
theorem stateRows_eq8_1_3 : stateRows8_1_3 = final8_1_3.map (List.map Prod.snd) := by
  simp only [stateRows8_1_3, final8_1_3, List.map_cons, List.map_nil, patch_states8_1_3_0, patch_states8_1_3_1, patch_states8_1_3_3, patch_states8_1_3_4, patch_states8_1_3_5, patch_states8_1_3_6, patch_states8_1_3_7, patch_states8_1_3_8, patch_states8_1_3_9, patch_states8_1_3_10, patch_states8_1_3_11]
theorem final_states8_1_3 : final8_1_3 = stateRows8_1_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
