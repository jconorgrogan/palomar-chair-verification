module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart046
public import SpectreFinite.ParentOwnershipFinitePart088

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_1_1_0 : List State := ParentOwnership.parentRow1420
def patch5_1_1_0 : Patch := literalDomain.zip stateRow5_1_1_0
theorem patch_states5_1_1_0 : patch5_1_1_0.map Prod.snd = stateRow5_1_1_0 := by rfl
def stateRow5_1_1_1 : List State := ParentOwnership.parentRow0744
def patch5_1_1_1 : Patch := literalDomain.zip stateRow5_1_1_1
theorem patch_states5_1_1_1 : patch5_1_1_1.map Prod.snd = stateRow5_1_1_1 := by rfl
def stateRow5_1_1_3 : List State := ParentOwnership.parentRow0748
def patch5_1_1_3 : Patch := literalDomain.zip stateRow5_1_1_3
theorem patch_states5_1_1_3 : patch5_1_1_3.map Prod.snd = stateRow5_1_1_3 := by rfl
def stateRow5_1_1_4 : List State := ParentOwnership.parentRow0747
def patch5_1_1_4 : Patch := literalDomain.zip stateRow5_1_1_4
theorem patch_states5_1_1_4 : patch5_1_1_4.map Prod.snd = stateRow5_1_1_4 := by rfl
def stateRow5_1_1_7 : List State := ParentOwnership.parentRow0743
def patch5_1_1_7 : Patch := literalDomain.zip stateRow5_1_1_7
theorem patch_states5_1_1_7 : patch5_1_1_7.map Prod.snd = stateRow5_1_1_7 := by rfl
def stateRow5_1_1_8 : List State := ParentOwnership.parentRow0745
def patch5_1_1_8 : Patch := literalDomain.zip stateRow5_1_1_8
theorem patch_states5_1_1_8 : patch5_1_1_8.map Prod.snd = stateRow5_1_1_8 := by rfl
def stateRow5_1_1_9 : List State := ParentOwnership.parentRow0746
def patch5_1_1_9 : Patch := literalDomain.zip stateRow5_1_1_9
theorem patch_states5_1_1_9 : patch5_1_1_9.map Prod.snd = stateRow5_1_1_9 := by rfl
def stateRow5_1_1_11 : List State := ParentOwnership.parentRow0751
def patch5_1_1_11 : Patch := literalDomain.zip stateRow5_1_1_11
theorem patch_states5_1_1_11 : patch5_1_1_11.map Prod.snd = stateRow5_1_1_11 := by rfl
def final5_1_1 : List Patch := [patch5_1_1_0, patch5_1_1_1, patch5_1_1_3, patch5_1_1_4, patch5_1_1_7, patch5_1_1_8, patch5_1_1_9, patch5_1_1_11]
def stateRows5_1_1 : List (List State) := [stateRow5_1_1_0, stateRow5_1_1_1, stateRow5_1_1_3, stateRow5_1_1_4, stateRow5_1_1_7, stateRow5_1_1_8, stateRow5_1_1_9, stateRow5_1_1_11]
theorem stateRows_eq5_1_1 : stateRows5_1_1 = final5_1_1.map (List.map Prod.snd) := by
  simp only [stateRows5_1_1, final5_1_1, List.map_cons, List.map_nil, patch_states5_1_1_0, patch_states5_1_1_1, patch_states5_1_1_3, patch_states5_1_1_4, patch_states5_1_1_7, patch_states5_1_1_8, patch_states5_1_1_9, patch_states5_1_1_11]
theorem final_states5_1_1 : final5_1_1 = stateRows5_1_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
