module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart035
public import SpectreFinite.ParentOwnershipFinitePart036
public import SpectreFinite.ParentOwnershipFinitePart045
public import SpectreFinite.ParentOwnershipFinitePart050
public import SpectreFinite.ParentOwnershipFinitePart088

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_1_0_2 : List State := ParentOwnership.parentRow0725
def patch5_1_0_2 : Patch := literalDomain.zip stateRow5_1_0_2
theorem patch_states5_1_0_2 : patch5_1_0_2.map Prod.snd = stateRow5_1_0_2 := by rfl
def stateRow5_1_0_3 : List State := ParentOwnership.parentRow0570
def patch5_1_0_3 : Patch := literalDomain.zip stateRow5_1_0_3
theorem patch_states5_1_0_3 : patch5_1_0_3.map Prod.snd = stateRow5_1_0_3 := by rfl
def stateRow5_1_0_4 : List State := ParentOwnership.parentRow0802
def patch5_1_0_4 : Patch := literalDomain.zip stateRow5_1_0_4
theorem patch_states5_1_0_4 : patch5_1_0_4.map Prod.snd = stateRow5_1_0_4 := by rfl
def stateRow5_1_0_6 : List State := ParentOwnership.parentRow0583
def patch5_1_0_6 : Patch := literalDomain.zip stateRow5_1_0_6
theorem patch_states5_1_0_6 : patch5_1_0_6.map Prod.snd = stateRow5_1_0_6 := by rfl
def stateRow5_1_0_7 : List State := ParentOwnership.parentRow0800
def patch5_1_0_7 : Patch := literalDomain.zip stateRow5_1_0_7
theorem patch_states5_1_0_7 : patch5_1_0_7.map Prod.snd = stateRow5_1_0_7 := by rfl
def stateRow5_1_0_9 : List State := ParentOwnership.parentRow1414
def patch5_1_0_9 : Patch := literalDomain.zip stateRow5_1_0_9
theorem patch_states5_1_0_9 : patch5_1_0_9.map Prod.snd = stateRow5_1_0_9 := by rfl
def stateRow5_1_0_10 : List State := ParentOwnership.parentRow1416
def patch5_1_0_10 : Patch := literalDomain.zip stateRow5_1_0_10
theorem patch_states5_1_0_10 : patch5_1_0_10.map Prod.snd = stateRow5_1_0_10 := by rfl
def stateRow5_1_0_11 : List State := ParentOwnership.parentRow1415
def patch5_1_0_11 : Patch := literalDomain.zip stateRow5_1_0_11
theorem patch_states5_1_0_11 : patch5_1_0_11.map Prod.snd = stateRow5_1_0_11 := by rfl
def final5_1_0 : List Patch := [patch5_1_0_2, patch5_1_0_3, patch5_1_0_4, patch5_1_0_6, patch5_1_0_7, patch5_1_0_9, patch5_1_0_10, patch5_1_0_11]
def stateRows5_1_0 : List (List State) := [stateRow5_1_0_2, stateRow5_1_0_3, stateRow5_1_0_4, stateRow5_1_0_6, stateRow5_1_0_7, stateRow5_1_0_9, stateRow5_1_0_10, stateRow5_1_0_11]
theorem stateRows_eq5_1_0 : stateRows5_1_0 = final5_1_0.map (List.map Prod.snd) := by
  simp only [stateRows5_1_0, final5_1_0, List.map_cons, List.map_nil, patch_states5_1_0_2, patch_states5_1_0_3, patch_states5_1_0_4, patch_states5_1_0_6, patch_states5_1_0_7, patch_states5_1_0_9, patch_states5_1_0_10, patch_states5_1_0_11]
theorem final_states5_1_0 : final5_1_0 = stateRows5_1_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
