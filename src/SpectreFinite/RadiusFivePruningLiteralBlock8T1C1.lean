module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart122
public import SpectreFinite.ParentOwnershipFinitePart123

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_1_1_0 : List State := ParentOwnership.parentRow1965
def patch8_1_1_0 : Patch := literalDomain.zip stateRow8_1_1_0
theorem patch_states8_1_1_0 : patch8_1_1_0.map Prod.snd = stateRow8_1_1_0 := by rfl
def stateRow8_1_1_1 : List State := ParentOwnership.parentRow1968
def patch8_1_1_1 : Patch := literalDomain.zip stateRow8_1_1_1
theorem patch_states8_1_1_1 : patch8_1_1_1.map Prod.snd = stateRow8_1_1_1 := by rfl
def stateRow8_1_1_2 : List State := ParentOwnership.parentRow1973
def patch8_1_1_2 : Patch := literalDomain.zip stateRow8_1_1_2
theorem patch_states8_1_1_2 : patch8_1_1_2.map Prod.snd = stateRow8_1_1_2 := by rfl
def stateRow8_1_1_3 : List State := ParentOwnership.parentRow1966
def patch8_1_1_3 : Patch := literalDomain.zip stateRow8_1_1_3
theorem patch_states8_1_1_3 : patch8_1_1_3.map Prod.snd = stateRow8_1_1_3 := by rfl
def stateRow8_1_1_4 : List State := ParentOwnership.parentRow1967
def patch8_1_1_4 : Patch := literalDomain.zip stateRow8_1_1_4
theorem patch_states8_1_1_4 : patch8_1_1_4.map Prod.snd = stateRow8_1_1_4 := by rfl
def stateRow8_1_1_6 : List State := ParentOwnership.parentRow1969
def patch8_1_1_6 : Patch := literalDomain.zip stateRow8_1_1_6
theorem patch_states8_1_1_6 : patch8_1_1_6.map Prod.snd = stateRow8_1_1_6 := by rfl
def stateRow8_1_1_8 : List State := ParentOwnership.parentRow1974
def patch8_1_1_8 : Patch := literalDomain.zip stateRow8_1_1_8
theorem patch_states8_1_1_8 : patch8_1_1_8.map Prod.snd = stateRow8_1_1_8 := by rfl
def stateRow8_1_1_9 : List State := ParentOwnership.parentRow1970
def patch8_1_1_9 : Patch := literalDomain.zip stateRow8_1_1_9
theorem patch_states8_1_1_9 : patch8_1_1_9.map Prod.snd = stateRow8_1_1_9 := by rfl
def stateRow8_1_1_10 : List State := ParentOwnership.parentRow1975
def patch8_1_1_10 : Patch := literalDomain.zip stateRow8_1_1_10
theorem patch_states8_1_1_10 : patch8_1_1_10.map Prod.snd = stateRow8_1_1_10 := by rfl
def final8_1_1 : List Patch := [patch8_1_1_0, patch8_1_1_1, patch8_1_1_2, patch8_1_1_3, patch8_1_1_4, patch8_1_1_6, patch8_1_1_8, patch8_1_1_9, patch8_1_1_10]
def stateRows8_1_1 : List (List State) := [stateRow8_1_1_0, stateRow8_1_1_1, stateRow8_1_1_2, stateRow8_1_1_3, stateRow8_1_1_4, stateRow8_1_1_6, stateRow8_1_1_8, stateRow8_1_1_9, stateRow8_1_1_10]
theorem stateRows_eq8_1_1 : stateRows8_1_1 = final8_1_1.map (List.map Prod.snd) := by
  simp only [stateRows8_1_1, final8_1_1, List.map_cons, List.map_nil, patch_states8_1_1_0, patch_states8_1_1_1, patch_states8_1_1_2, patch_states8_1_1_3, patch_states8_1_1_4, patch_states8_1_1_6, patch_states8_1_1_8, patch_states8_1_1_9, patch_states8_1_1_10]
theorem final_states8_1_1 : final8_1_1 = stateRows8_1_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
