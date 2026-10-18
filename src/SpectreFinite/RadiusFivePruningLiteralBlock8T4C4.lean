module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart042
public import SpectreFinite.ParentOwnershipFinitePart087
public import SpectreFinite.ParentOwnershipFinitePart114
public import SpectreFinite.ParentOwnershipFinitePart115

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_4_4_0 : List State := ParentOwnership.parentRow1836
def patch8_4_4_0 : Patch := literalDomain.zip stateRow8_4_4_0
theorem patch_states8_4_4_0 : patch8_4_4_0.map Prod.snd = stateRow8_4_4_0 := by rfl
def stateRow8_4_4_1 : List State := ParentOwnership.parentRow0674
def patch8_4_4_1 : Patch := literalDomain.zip stateRow8_4_4_1
theorem patch_states8_4_4_1 : patch8_4_4_1.map Prod.snd = stateRow8_4_4_1 := by rfl
def stateRow8_4_4_2 : List State := ParentOwnership.parentRow1841
def patch8_4_4_2 : Patch := literalDomain.zip stateRow8_4_4_2
theorem patch_states8_4_4_2 : patch8_4_4_2.map Prod.snd = stateRow8_4_4_2 := by rfl
def stateRow8_4_4_3 : List State := ParentOwnership.parentRow0675
def patch8_4_4_3 : Patch := literalDomain.zip stateRow8_4_4_3
theorem patch_states8_4_4_3 : patch8_4_4_3.map Prod.snd = stateRow8_4_4_3 := by rfl
def stateRow8_4_4_4 : List State := ParentOwnership.parentRow1842
def patch8_4_4_4 : Patch := literalDomain.zip stateRow8_4_4_4
theorem patch_states8_4_4_4 : patch8_4_4_4.map Prod.snd = stateRow8_4_4_4 := by rfl
def stateRow8_4_4_5 : List State := ParentOwnership.parentRow1847
def patch8_4_4_5 : Patch := literalDomain.zip stateRow8_4_4_5
theorem patch_states8_4_4_5 : patch8_4_4_5.map Prod.snd = stateRow8_4_4_5 := by rfl
def stateRow8_4_4_8 : List State := ParentOwnership.parentRow1397
def patch8_4_4_8 : Patch := literalDomain.zip stateRow8_4_4_8
theorem patch_states8_4_4_8 : patch8_4_4_8.map Prod.snd = stateRow8_4_4_8 := by rfl
def stateRow8_4_4_9 : List State := ParentOwnership.parentRow1845
def patch8_4_4_9 : Patch := literalDomain.zip stateRow8_4_4_9
theorem patch_states8_4_4_9 : patch8_4_4_9.map Prod.snd = stateRow8_4_4_9 := by rfl
def stateRow8_4_4_10 : List State := ParentOwnership.parentRow1850
def patch8_4_4_10 : Patch := literalDomain.zip stateRow8_4_4_10
theorem patch_states8_4_4_10 : patch8_4_4_10.map Prod.snd = stateRow8_4_4_10 := by rfl
def stateRow8_4_4_11 : List State := ParentOwnership.parentRow1846
def patch8_4_4_11 : Patch := literalDomain.zip stateRow8_4_4_11
theorem patch_states8_4_4_11 : patch8_4_4_11.map Prod.snd = stateRow8_4_4_11 := by rfl
def final8_4_4 : List Patch := [patch8_4_4_0, patch8_4_4_1, patch8_4_4_2, patch8_4_4_3, patch8_4_4_4, patch8_4_4_5, patch8_4_4_8, patch8_4_4_9, patch8_4_4_10, patch8_4_4_11]
def stateRows8_4_4 : List (List State) := [stateRow8_4_4_0, stateRow8_4_4_1, stateRow8_4_4_2, stateRow8_4_4_3, stateRow8_4_4_4, stateRow8_4_4_5, stateRow8_4_4_8, stateRow8_4_4_9, stateRow8_4_4_10, stateRow8_4_4_11]
theorem stateRows_eq8_4_4 : stateRows8_4_4 = final8_4_4.map (List.map Prod.snd) := by
  simp only [stateRows8_4_4, final8_4_4, List.map_cons, List.map_nil, patch_states8_4_4_0, patch_states8_4_4_1, patch_states8_4_4_2, patch_states8_4_4_3, patch_states8_4_4_4, patch_states8_4_4_5, patch_states8_4_4_8, patch_states8_4_4_9, patch_states8_4_4_10, patch_states8_4_4_11]
theorem final_states8_4_4 : final8_4_4 = stateRows8_4_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
