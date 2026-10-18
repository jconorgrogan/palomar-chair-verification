module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart058
public import SpectreFinite.ParentOwnershipFinitePart122
public import SpectreFinite.ParentOwnershipFinitePart123
public import SpectreFinite.ParentOwnershipFinitePart124
public import SpectreFinite.ParentOwnershipFinitePart125

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_1_0_1 : List State := ParentOwnership.parentRow1997
def patch8_1_0_1 : Patch := literalDomain.zip stateRow8_1_0_1
theorem patch_states8_1_0_1 : patch8_1_0_1.map Prod.snd = stateRow8_1_0_1 := by rfl
def stateRow8_1_0_3 : List State := ParentOwnership.parentRow0934
def patch8_1_0_3 : Patch := literalDomain.zip stateRow8_1_0_3
theorem patch_states8_1_0_3 : patch8_1_0_3.map Prod.snd = stateRow8_1_0_3 := by rfl
def stateRow8_1_0_4 : List State := ParentOwnership.parentRow1998
def patch8_1_0_4 : Patch := literalDomain.zip stateRow8_1_0_4
theorem patch_states8_1_0_4 : patch8_1_0_4.map Prod.snd = stateRow8_1_0_4 := by rfl
def stateRow8_1_0_5 : List State := ParentOwnership.parentRow1999
def patch8_1_0_5 : Patch := literalDomain.zip stateRow8_1_0_5
theorem patch_states8_1_0_5 : patch8_1_0_5.map Prod.snd = stateRow8_1_0_5 := by rfl
def stateRow8_1_0_6 : List State := ParentOwnership.parentRow2000
def patch8_1_0_6 : Patch := literalDomain.zip stateRow8_1_0_6
theorem patch_states8_1_0_6 : patch8_1_0_6.map Prod.snd = stateRow8_1_0_6 := by rfl
def stateRow8_1_0_7 : List State := ParentOwnership.parentRow1971
def patch8_1_0_7 : Patch := literalDomain.zip stateRow8_1_0_7
theorem patch_states8_1_0_7 : patch8_1_0_7.map Prod.snd = stateRow8_1_0_7 := by rfl
def stateRow8_1_0_8 : List State := ParentOwnership.parentRow1976
def patch8_1_0_8 : Patch := literalDomain.zip stateRow8_1_0_8
theorem patch_states8_1_0_8 : patch8_1_0_8.map Prod.snd = stateRow8_1_0_8 := by rfl
def stateRow8_1_0_9 : List State := ParentOwnership.parentRow1963
def patch8_1_0_9 : Patch := literalDomain.zip stateRow8_1_0_9
theorem patch_states8_1_0_9 : patch8_1_0_9.map Prod.snd = stateRow8_1_0_9 := by rfl
def stateRow8_1_0_10 : List State := ParentOwnership.parentRow1972
def patch8_1_0_10 : Patch := literalDomain.zip stateRow8_1_0_10
theorem patch_states8_1_0_10 : patch8_1_0_10.map Prod.snd = stateRow8_1_0_10 := by rfl
def stateRow8_1_0_11 : List State := ParentOwnership.parentRow1964
def patch8_1_0_11 : Patch := literalDomain.zip stateRow8_1_0_11
theorem patch_states8_1_0_11 : patch8_1_0_11.map Prod.snd = stateRow8_1_0_11 := by rfl
def final8_1_0 : List Patch := [patch8_1_0_1, patch8_1_0_3, patch8_1_0_4, patch8_1_0_5, patch8_1_0_6, patch8_1_0_7, patch8_1_0_8, patch8_1_0_9, patch8_1_0_10, patch8_1_0_11]
def stateRows8_1_0 : List (List State) := [stateRow8_1_0_1, stateRow8_1_0_3, stateRow8_1_0_4, stateRow8_1_0_5, stateRow8_1_0_6, stateRow8_1_0_7, stateRow8_1_0_8, stateRow8_1_0_9, stateRow8_1_0_10, stateRow8_1_0_11]
theorem stateRows_eq8_1_0 : stateRows8_1_0 = final8_1_0.map (List.map Prod.snd) := by
  simp only [stateRows8_1_0, final8_1_0, List.map_cons, List.map_nil, patch_states8_1_0_1, patch_states8_1_0_3, patch_states8_1_0_4, patch_states8_1_0_5, patch_states8_1_0_6, patch_states8_1_0_7, patch_states8_1_0_8, patch_states8_1_0_9, patch_states8_1_0_10, patch_states8_1_0_11]
theorem final_states8_1_0 : final8_1_0 = stateRows8_1_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
