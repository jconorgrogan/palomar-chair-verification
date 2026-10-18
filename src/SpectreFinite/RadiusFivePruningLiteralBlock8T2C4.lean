module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart023
public import SpectreFinite.ParentOwnershipFinitePart024
public import SpectreFinite.ParentOwnershipFinitePart025
public import SpectreFinite.ParentOwnershipFinitePart094

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_2_4_0 : List State := ParentOwnership.parentRow1513
def patch8_2_4_0 : Patch := literalDomain.zip stateRow8_2_4_0
theorem patch_states8_2_4_0 : patch8_2_4_0.map Prod.snd = stateRow8_2_4_0 := by rfl
def stateRow8_2_4_1 : List State := ParentOwnership.parentRow0407
def patch8_2_4_1 : Patch := literalDomain.zip stateRow8_2_4_1
theorem patch_states8_2_4_1 : patch8_2_4_1.map Prod.snd = stateRow8_2_4_1 := by rfl
def stateRow8_2_4_2 : List State := ParentOwnership.parentRow0405
def patch8_2_4_2 : Patch := literalDomain.zip stateRow8_2_4_2
theorem patch_states8_2_4_2 : patch8_2_4_2.map Prod.snd = stateRow8_2_4_2 := by rfl
def stateRow8_2_4_3 : List State := ParentOwnership.parentRow0408
def patch8_2_4_3 : Patch := literalDomain.zip stateRow8_2_4_3
theorem patch_states8_2_4_3 : patch8_2_4_3.map Prod.snd = stateRow8_2_4_3 := by rfl
def stateRow8_2_4_4 : List State := ParentOwnership.parentRow0406
def patch8_2_4_4 : Patch := literalDomain.zip stateRow8_2_4_4
theorem patch_states8_2_4_4 : patch8_2_4_4.map Prod.snd = stateRow8_2_4_4 := by rfl
def stateRow8_2_4_5 : List State := ParentOwnership.parentRow0398
def patch8_2_4_5 : Patch := literalDomain.zip stateRow8_2_4_5
theorem patch_states8_2_4_5 : patch8_2_4_5.map Prod.snd = stateRow8_2_4_5 := by rfl
def stateRow8_2_4_8 : List State := ParentOwnership.parentRow0375
def patch8_2_4_8 : Patch := literalDomain.zip stateRow8_2_4_8
theorem patch_states8_2_4_8 : patch8_2_4_8.map Prod.snd = stateRow8_2_4_8 := by rfl
def stateRow8_2_4_9 : List State := ParentOwnership.parentRow0383
def patch8_2_4_9 : Patch := literalDomain.zip stateRow8_2_4_9
theorem patch_states8_2_4_9 : patch8_2_4_9.map Prod.snd = stateRow8_2_4_9 := by rfl
def stateRow8_2_4_10 : List State := ParentOwnership.parentRow0384
def patch8_2_4_10 : Patch := literalDomain.zip stateRow8_2_4_10
theorem patch_states8_2_4_10 : patch8_2_4_10.map Prod.snd = stateRow8_2_4_10 := by rfl
def stateRow8_2_4_11 : List State := ParentOwnership.parentRow1510
def patch8_2_4_11 : Patch := literalDomain.zip stateRow8_2_4_11
theorem patch_states8_2_4_11 : patch8_2_4_11.map Prod.snd = stateRow8_2_4_11 := by rfl
def final8_2_4 : List Patch := [patch8_2_4_0, patch8_2_4_1, patch8_2_4_2, patch8_2_4_3, patch8_2_4_4, patch8_2_4_5, patch8_2_4_8, patch8_2_4_9, patch8_2_4_10, patch8_2_4_11]
def stateRows8_2_4 : List (List State) := [stateRow8_2_4_0, stateRow8_2_4_1, stateRow8_2_4_2, stateRow8_2_4_3, stateRow8_2_4_4, stateRow8_2_4_5, stateRow8_2_4_8, stateRow8_2_4_9, stateRow8_2_4_10, stateRow8_2_4_11]
theorem stateRows_eq8_2_4 : stateRows8_2_4 = final8_2_4.map (List.map Prod.snd) := by
  simp only [stateRows8_2_4, final8_2_4, List.map_cons, List.map_nil, patch_states8_2_4_0, patch_states8_2_4_1, patch_states8_2_4_2, patch_states8_2_4_3, patch_states8_2_4_4, patch_states8_2_4_5, patch_states8_2_4_8, patch_states8_2_4_9, patch_states8_2_4_10, patch_states8_2_4_11]
theorem final_states8_2_4 : final8_2_4 = stateRows8_2_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
