module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart044
public import SpectreFinite.ParentOwnershipFinitePart045

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_0_0_1 : List State := ParentOwnership.parentRow0704
def patch1_0_0_1 : Patch := literalDomain.zip stateRow1_0_0_1
theorem patch_states1_0_0_1 : patch1_0_0_1.map Prod.snd = stateRow1_0_0_1 := by rfl
def stateRow1_0_0_2 : List State := ParentOwnership.parentRow0705
def patch1_0_0_2 : Patch := literalDomain.zip stateRow1_0_0_2
theorem patch_states1_0_0_2 : patch1_0_0_2.map Prod.snd = stateRow1_0_0_2 := by rfl
def stateRow1_0_0_3 : List State := ParentOwnership.parentRow0706
def patch1_0_0_3 : Patch := literalDomain.zip stateRow1_0_0_3
theorem patch_states1_0_0_3 : patch1_0_0_3.map Prod.snd = stateRow1_0_0_3 := by rfl
def stateRow1_0_0_5 : List State := ParentOwnership.parentRow0707
def patch1_0_0_5 : Patch := literalDomain.zip stateRow1_0_0_5
theorem patch_states1_0_0_5 : patch1_0_0_5.map Prod.snd = stateRow1_0_0_5 := by rfl
def stateRow1_0_0_6 : List State := ParentOwnership.parentRow0708
def patch1_0_0_6 : Patch := literalDomain.zip stateRow1_0_0_6
theorem patch_states1_0_0_6 : patch1_0_0_6.map Prod.snd = stateRow1_0_0_6 := by rfl
def stateRow1_0_0_7 : List State := ParentOwnership.parentRow0709
def patch1_0_0_7 : Patch := literalDomain.zip stateRow1_0_0_7
theorem patch_states1_0_0_7 : patch1_0_0_7.map Prod.snd = stateRow1_0_0_7 := by rfl
def stateRow1_0_0_8 : List State := ParentOwnership.parentRow0710
def patch1_0_0_8 : Patch := literalDomain.zip stateRow1_0_0_8
theorem patch_states1_0_0_8 : patch1_0_0_8.map Prod.snd = stateRow1_0_0_8 := by rfl
def stateRow1_0_0_9 : List State := ParentOwnership.parentRow0711
def patch1_0_0_9 : Patch := literalDomain.zip stateRow1_0_0_9
theorem patch_states1_0_0_9 : patch1_0_0_9.map Prod.snd = stateRow1_0_0_9 := by rfl
def stateRow1_0_0_10 : List State := ParentOwnership.parentRow0719
def patch1_0_0_10 : Patch := literalDomain.zip stateRow1_0_0_10
theorem patch_states1_0_0_10 : patch1_0_0_10.map Prod.snd = stateRow1_0_0_10 := by rfl
def stateRow1_0_0_11 : List State := ParentOwnership.parentRow0720
def patch1_0_0_11 : Patch := literalDomain.zip stateRow1_0_0_11
theorem patch_states1_0_0_11 : patch1_0_0_11.map Prod.snd = stateRow1_0_0_11 := by rfl
def final1_0_0 : List Patch := [patch1_0_0_1, patch1_0_0_2, patch1_0_0_3, patch1_0_0_5, patch1_0_0_6, patch1_0_0_7, patch1_0_0_8, patch1_0_0_9, patch1_0_0_10, patch1_0_0_11]
def stateRows1_0_0 : List (List State) := [stateRow1_0_0_1, stateRow1_0_0_2, stateRow1_0_0_3, stateRow1_0_0_5, stateRow1_0_0_6, stateRow1_0_0_7, stateRow1_0_0_8, stateRow1_0_0_9, stateRow1_0_0_10, stateRow1_0_0_11]
theorem stateRows_eq1_0_0 : stateRows1_0_0 = final1_0_0.map (List.map Prod.snd) := by
  simp only [stateRows1_0_0, final1_0_0, List.map_cons, List.map_nil, patch_states1_0_0_1, patch_states1_0_0_2, patch_states1_0_0_3, patch_states1_0_0_5, patch_states1_0_0_6, patch_states1_0_0_7, patch_states1_0_0_8, patch_states1_0_0_9, patch_states1_0_0_10, patch_states1_0_0_11]
theorem final_states1_0_0 : final1_0_0 = stateRows1_0_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
