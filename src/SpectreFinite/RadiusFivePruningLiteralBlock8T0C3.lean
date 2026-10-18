module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart037
public import SpectreFinite.ParentOwnershipFinitePart038
public import SpectreFinite.ParentOwnershipFinitePart125
public import SpectreFinite.ParentOwnershipFinitePart126

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_0_3_0 : List State := ParentOwnership.parentRow2009
def patch8_0_3_0 : Patch := literalDomain.zip stateRow8_0_3_0
theorem patch_states8_0_3_0 : patch8_0_3_0.map Prod.snd = stateRow8_0_3_0 := by rfl
def stateRow8_0_3_1 : List State := ParentOwnership.parentRow2010
def patch8_0_3_1 : Patch := literalDomain.zip stateRow8_0_3_1
theorem patch_states8_0_3_1 : patch8_0_3_1.map Prod.snd = stateRow8_0_3_1 := by rfl
def stateRow8_0_3_3 : List State := ParentOwnership.parentRow2014
def patch8_0_3_3 : Patch := literalDomain.zip stateRow8_0_3_3
theorem patch_states8_0_3_3 : patch8_0_3_3.map Prod.snd = stateRow8_0_3_3 := by rfl
def stateRow8_0_3_4 : List State := ParentOwnership.parentRow2015
def patch8_0_3_4 : Patch := literalDomain.zip stateRow8_0_3_4
theorem patch_states8_0_3_4 : patch8_0_3_4.map Prod.snd = stateRow8_0_3_4 := by rfl
def stateRow8_0_3_5 : List State := ParentOwnership.parentRow2016
def patch8_0_3_5 : Patch := literalDomain.zip stateRow8_0_3_5
theorem patch_states8_0_3_5 : patch8_0_3_5.map Prod.snd = stateRow8_0_3_5 := by rfl
def stateRow8_0_3_6 : List State := ParentOwnership.parentRow2017
def patch8_0_3_6 : Patch := literalDomain.zip stateRow8_0_3_6
theorem patch_states8_0_3_6 : patch8_0_3_6.map Prod.snd = stateRow8_0_3_6 := by rfl
def stateRow8_0_3_7 : List State := ParentOwnership.parentRow0606
def patch8_0_3_7 : Patch := literalDomain.zip stateRow8_0_3_7
theorem patch_states8_0_3_7 : patch8_0_3_7.map Prod.snd = stateRow8_0_3_7 := by rfl
def stateRow8_0_3_8 : List State := ParentOwnership.parentRow0607
def patch8_0_3_8 : Patch := literalDomain.zip stateRow8_0_3_8
theorem patch_states8_0_3_8 : patch8_0_3_8.map Prod.snd = stateRow8_0_3_8 := by rfl
def stateRow8_0_3_9 : List State := ParentOwnership.parentRow0609
def patch8_0_3_9 : Patch := literalDomain.zip stateRow8_0_3_9
theorem patch_states8_0_3_9 : patch8_0_3_9.map Prod.snd = stateRow8_0_3_9 := by rfl
def stateRow8_0_3_10 : List State := ParentOwnership.parentRow0610
def patch8_0_3_10 : Patch := literalDomain.zip stateRow8_0_3_10
theorem patch_states8_0_3_10 : patch8_0_3_10.map Prod.snd = stateRow8_0_3_10 := by rfl
def stateRow8_0_3_11 : List State := ParentOwnership.parentRow0611
def patch8_0_3_11 : Patch := literalDomain.zip stateRow8_0_3_11
theorem patch_states8_0_3_11 : patch8_0_3_11.map Prod.snd = stateRow8_0_3_11 := by rfl
def final8_0_3 : List Patch := [patch8_0_3_0, patch8_0_3_1, patch8_0_3_3, patch8_0_3_4, patch8_0_3_5, patch8_0_3_6, patch8_0_3_7, patch8_0_3_8, patch8_0_3_9, patch8_0_3_10, patch8_0_3_11]
def stateRows8_0_3 : List (List State) := [stateRow8_0_3_0, stateRow8_0_3_1, stateRow8_0_3_3, stateRow8_0_3_4, stateRow8_0_3_5, stateRow8_0_3_6, stateRow8_0_3_7, stateRow8_0_3_8, stateRow8_0_3_9, stateRow8_0_3_10, stateRow8_0_3_11]
theorem stateRows_eq8_0_3 : stateRows8_0_3 = final8_0_3.map (List.map Prod.snd) := by
  simp only [stateRows8_0_3, final8_0_3, List.map_cons, List.map_nil, patch_states8_0_3_0, patch_states8_0_3_1, patch_states8_0_3_3, patch_states8_0_3_4, patch_states8_0_3_5, patch_states8_0_3_6, patch_states8_0_3_7, patch_states8_0_3_8, patch_states8_0_3_9, patch_states8_0_3_10, patch_states8_0_3_11]
theorem final_states8_0_3 : final8_0_3 = stateRows8_0_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
