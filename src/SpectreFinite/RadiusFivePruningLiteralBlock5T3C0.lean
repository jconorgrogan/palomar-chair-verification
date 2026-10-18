module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart003
public import SpectreFinite.ParentOwnershipFinitePart030
public import SpectreFinite.ParentOwnershipFinitePart100

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_3_0_2 : List State := ParentOwnership.parentRow1610
def patch5_3_0_2 : Patch := literalDomain.zip stateRow5_3_0_2
theorem patch_states5_3_0_2 : patch5_3_0_2.map Prod.snd = stateRow5_3_0_2 := by rfl
def stateRow5_3_0_3 : List State := ParentOwnership.parentRow1609
def patch5_3_0_3 : Patch := literalDomain.zip stateRow5_3_0_3
theorem patch_states5_3_0_3 : patch5_3_0_3.map Prod.snd = stateRow5_3_0_3 := by rfl
def stateRow5_3_0_4 : List State := ParentOwnership.parentRow1608
def patch5_3_0_4 : Patch := literalDomain.zip stateRow5_3_0_4
theorem patch_states5_3_0_4 : patch5_3_0_4.map Prod.snd = stateRow5_3_0_4 := by rfl
def stateRow5_3_0_6 : List State := ParentOwnership.parentRow1612
def patch5_3_0_6 : Patch := literalDomain.zip stateRow5_3_0_6
theorem patch_states5_3_0_6 : patch5_3_0_6.map Prod.snd = stateRow5_3_0_6 := by rfl
def stateRow5_3_0_7 : List State := ParentOwnership.parentRow1611
def patch5_3_0_7 : Patch := literalDomain.zip stateRow5_3_0_7
theorem patch_states5_3_0_7 : patch5_3_0_7.map Prod.snd = stateRow5_3_0_7 := by rfl
def stateRow5_3_0_9 : List State := ParentOwnership.parentRow0487
def patch5_3_0_9 : Patch := literalDomain.zip stateRow5_3_0_9
theorem patch_states5_3_0_9 : patch5_3_0_9.map Prod.snd = stateRow5_3_0_9 := by rfl
def stateRow5_3_0_10 : List State := ParentOwnership.parentRow0058
def patch5_3_0_10 : Patch := literalDomain.zip stateRow5_3_0_10
theorem patch_states5_3_0_10 : patch5_3_0_10.map Prod.snd = stateRow5_3_0_10 := by rfl
def stateRow5_3_0_11 : List State := ParentOwnership.parentRow0493
def patch5_3_0_11 : Patch := literalDomain.zip stateRow5_3_0_11
theorem patch_states5_3_0_11 : patch5_3_0_11.map Prod.snd = stateRow5_3_0_11 := by rfl
def final5_3_0 : List Patch := [patch5_3_0_2, patch5_3_0_3, patch5_3_0_4, patch5_3_0_6, patch5_3_0_7, patch5_3_0_9, patch5_3_0_10, patch5_3_0_11]
def stateRows5_3_0 : List (List State) := [stateRow5_3_0_2, stateRow5_3_0_3, stateRow5_3_0_4, stateRow5_3_0_6, stateRow5_3_0_7, stateRow5_3_0_9, stateRow5_3_0_10, stateRow5_3_0_11]
theorem stateRows_eq5_3_0 : stateRows5_3_0 = final5_3_0.map (List.map Prod.snd) := by
  simp only [stateRows5_3_0, final5_3_0, List.map_cons, List.map_nil, patch_states5_3_0_2, patch_states5_3_0_3, patch_states5_3_0_4, patch_states5_3_0_6, patch_states5_3_0_7, patch_states5_3_0_9, patch_states5_3_0_10, patch_states5_3_0_11]
theorem final_states5_3_0 : final5_3_0 = stateRows5_3_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
