module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart030
public import SpectreFinite.ParentOwnershipFinitePart031
public import SpectreFinite.ParentOwnershipFinitePart104

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_3_1_0 : List State := ParentOwnership.parentRow1665
def patch5_3_1_0 : Patch := literalDomain.zip stateRow5_3_1_0
theorem patch_states5_3_1_0 : patch5_3_1_0.map Prod.snd = stateRow5_3_1_0 := by rfl
def stateRow5_3_1_1 : List State := ParentOwnership.parentRow0508
def patch5_3_1_1 : Patch := literalDomain.zip stateRow5_3_1_1
theorem patch_states5_3_1_1 : patch5_3_1_1.map Prod.snd = stateRow5_3_1_1 := by rfl
def stateRow5_3_1_3 : List State := ParentOwnership.parentRow0501
def patch5_3_1_3 : Patch := literalDomain.zip stateRow5_3_1_3
theorem patch_states5_3_1_3 : patch5_3_1_3.map Prod.snd = stateRow5_3_1_3 := by rfl
def stateRow5_3_1_4 : List State := ParentOwnership.parentRow0486
def patch5_3_1_4 : Patch := literalDomain.zip stateRow5_3_1_4
theorem patch_states5_3_1_4 : patch5_3_1_4.map Prod.snd = stateRow5_3_1_4 := by rfl
def stateRow5_3_1_7 : List State := ParentOwnership.parentRow1669
def patch5_3_1_7 : Patch := literalDomain.zip stateRow5_3_1_7
theorem patch_states5_3_1_7 : patch5_3_1_7.map Prod.snd = stateRow5_3_1_7 := by rfl
def stateRow5_3_1_8 : List State := ParentOwnership.parentRow0490
def patch5_3_1_8 : Patch := literalDomain.zip stateRow5_3_1_8
theorem patch_states5_3_1_8 : patch5_3_1_8.map Prod.snd = stateRow5_3_1_8 := by rfl
def stateRow5_3_1_9 : List State := ParentOwnership.parentRow0494
def patch5_3_1_9 : Patch := literalDomain.zip stateRow5_3_1_9
theorem patch_states5_3_1_9 : patch5_3_1_9.map Prod.snd = stateRow5_3_1_9 := by rfl
def stateRow5_3_1_11 : List State := ParentOwnership.parentRow1666
def patch5_3_1_11 : Patch := literalDomain.zip stateRow5_3_1_11
theorem patch_states5_3_1_11 : patch5_3_1_11.map Prod.snd = stateRow5_3_1_11 := by rfl
def final5_3_1 : List Patch := [patch5_3_1_0, patch5_3_1_1, patch5_3_1_3, patch5_3_1_4, patch5_3_1_7, patch5_3_1_8, patch5_3_1_9, patch5_3_1_11]
def stateRows5_3_1 : List (List State) := [stateRow5_3_1_0, stateRow5_3_1_1, stateRow5_3_1_3, stateRow5_3_1_4, stateRow5_3_1_7, stateRow5_3_1_8, stateRow5_3_1_9, stateRow5_3_1_11]
theorem stateRows_eq5_3_1 : stateRows5_3_1 = final5_3_1.map (List.map Prod.snd) := by
  simp only [stateRows5_3_1, final5_3_1, List.map_cons, List.map_nil, patch_states5_3_1_0, patch_states5_3_1_1, patch_states5_3_1_3, patch_states5_3_1_4, patch_states5_3_1_7, patch_states5_3_1_8, patch_states5_3_1_9, patch_states5_3_1_11]
theorem final_states5_3_1 : final5_3_1 = stateRows5_3_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
