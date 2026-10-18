module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart014
public import SpectreFinite.ParentOwnershipFinitePart015
public import SpectreFinite.ParentOwnershipFinitePart016
public import SpectreFinite.ParentOwnershipFinitePart017
public import SpectreFinite.ParentOwnershipFinitePart074

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_5_4_0 : List State := ParentOwnership.parentRow1188
def patch8_5_4_0 : Patch := literalDomain.zip stateRow8_5_4_0
theorem patch_states8_5_4_0 : patch8_5_4_0.map Prod.snd = stateRow8_5_4_0 := by rfl
def stateRow8_5_4_1 : List State := ParentOwnership.parentRow0239
def patch8_5_4_1 : Patch := literalDomain.zip stateRow8_5_4_1
theorem patch_states8_5_4_1 : patch8_5_4_1.map Prod.snd = stateRow8_5_4_1 := by rfl
def stateRow8_5_4_2 : List State := ParentOwnership.parentRow0241
def patch8_5_4_2 : Patch := literalDomain.zip stateRow8_5_4_2
theorem patch_states8_5_4_2 : patch8_5_4_2.map Prod.snd = stateRow8_5_4_2 := by rfl
def stateRow8_5_4_3 : List State := ParentOwnership.parentRow0247
def patch8_5_4_3 : Patch := literalDomain.zip stateRow8_5_4_3
theorem patch_states8_5_4_3 : patch8_5_4_3.map Prod.snd = stateRow8_5_4_3 := by rfl
def stateRow8_5_4_4 : List State := ParentOwnership.parentRow0248
def patch8_5_4_4 : Patch := literalDomain.zip stateRow8_5_4_4
theorem patch_states8_5_4_4 : patch8_5_4_4.map Prod.snd = stateRow8_5_4_4 := by rfl
def stateRow8_5_4_5 : List State := ParentOwnership.parentRow0272
def patch8_5_4_5 : Patch := literalDomain.zip stateRow8_5_4_5
theorem patch_states8_5_4_5 : patch8_5_4_5.map Prod.snd = stateRow8_5_4_5 := by rfl
def stateRow8_5_4_8 : List State := ParentOwnership.parentRow0271
def patch8_5_4_8 : Patch := literalDomain.zip stateRow8_5_4_8
theorem patch_states8_5_4_8 : patch8_5_4_8.map Prod.snd = stateRow8_5_4_8 := by rfl
def stateRow8_5_4_9 : List State := ParentOwnership.parentRow0273
def patch8_5_4_9 : Patch := literalDomain.zip stateRow8_5_4_9
theorem patch_states8_5_4_9 : patch8_5_4_9.map Prod.snd = stateRow8_5_4_9 := by rfl
def stateRow8_5_4_10 : List State := ParentOwnership.parentRow0275
def patch8_5_4_10 : Patch := literalDomain.zip stateRow8_5_4_10
theorem patch_states8_5_4_10 : patch8_5_4_10.map Prod.snd = stateRow8_5_4_10 := by rfl
def stateRow8_5_4_11 : List State := ParentOwnership.parentRow0274
def patch8_5_4_11 : Patch := literalDomain.zip stateRow8_5_4_11
theorem patch_states8_5_4_11 : patch8_5_4_11.map Prod.snd = stateRow8_5_4_11 := by rfl
def final8_5_4 : List Patch := [patch8_5_4_0, patch8_5_4_1, patch8_5_4_2, patch8_5_4_3, patch8_5_4_4, patch8_5_4_5, patch8_5_4_8, patch8_5_4_9, patch8_5_4_10, patch8_5_4_11]
def stateRows8_5_4 : List (List State) := [stateRow8_5_4_0, stateRow8_5_4_1, stateRow8_5_4_2, stateRow8_5_4_3, stateRow8_5_4_4, stateRow8_5_4_5, stateRow8_5_4_8, stateRow8_5_4_9, stateRow8_5_4_10, stateRow8_5_4_11]
theorem stateRows_eq8_5_4 : stateRows8_5_4 = final8_5_4.map (List.map Prod.snd) := by
  simp only [stateRows8_5_4, final8_5_4, List.map_cons, List.map_nil, patch_states8_5_4_0, patch_states8_5_4_1, patch_states8_5_4_2, patch_states8_5_4_3, patch_states8_5_4_4, patch_states8_5_4_5, patch_states8_5_4_8, patch_states8_5_4_9, patch_states8_5_4_10, patch_states8_5_4_11]
theorem final_states8_5_4 : final8_5_4 = stateRows8_5_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
