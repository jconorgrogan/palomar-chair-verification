module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart023
public import SpectreFinite.ParentOwnershipFinitePart071
public import SpectreFinite.ParentOwnershipFinitePart072
public import SpectreFinite.ParentOwnershipFinitePart093

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_2_0_2 : List State := ParentOwnership.parentRow0377
def patch5_2_0_2 : Patch := literalDomain.zip stateRow5_2_0_2
theorem patch_states5_2_0_2 : patch5_2_0_2.map Prod.snd = stateRow5_2_0_2 := by rfl
def stateRow5_2_0_3 : List State := ParentOwnership.parentRow0376
def patch5_2_0_3 : Patch := literalDomain.zip stateRow5_2_0_3
theorem patch_states5_2_0_3 : patch5_2_0_3.map Prod.snd = stateRow5_2_0_3 := by rfl
def stateRow5_2_0_4 : List State := ParentOwnership.parentRow1494
def patch5_2_0_4 : Patch := literalDomain.zip stateRow5_2_0_4
theorem patch_states5_2_0_4 : patch5_2_0_4.map Prod.snd = stateRow5_2_0_4 := by rfl
def stateRow5_2_0_6 : List State := ParentOwnership.parentRow1495
def patch5_2_0_6 : Patch := literalDomain.zip stateRow5_2_0_6
theorem patch_states5_2_0_6 : patch5_2_0_6.map Prod.snd = stateRow5_2_0_6 := by rfl
def stateRow5_2_0_7 : List State := ParentOwnership.parentRow1493
def patch5_2_0_7 : Patch := literalDomain.zip stateRow5_2_0_7
theorem patch_states5_2_0_7 : patch5_2_0_7.map Prod.snd = stateRow5_2_0_7 := by rfl
def stateRow5_2_0_9 : List State := ParentOwnership.parentRow1145
def patch5_2_0_9 : Patch := literalDomain.zip stateRow5_2_0_9
theorem patch_states5_2_0_9 : patch5_2_0_9.map Prod.snd = stateRow5_2_0_9 := by rfl
def stateRow5_2_0_10 : List State := ParentOwnership.parentRow1153
def patch5_2_0_10 : Patch := literalDomain.zip stateRow5_2_0_10
theorem patch_states5_2_0_10 : patch5_2_0_10.map Prod.snd = stateRow5_2_0_10 := by rfl
def stateRow5_2_0_11 : List State := ParentOwnership.parentRow1146
def patch5_2_0_11 : Patch := literalDomain.zip stateRow5_2_0_11
theorem patch_states5_2_0_11 : patch5_2_0_11.map Prod.snd = stateRow5_2_0_11 := by rfl
def final5_2_0 : List Patch := [patch5_2_0_2, patch5_2_0_3, patch5_2_0_4, patch5_2_0_6, patch5_2_0_7, patch5_2_0_9, patch5_2_0_10, patch5_2_0_11]
def stateRows5_2_0 : List (List State) := [stateRow5_2_0_2, stateRow5_2_0_3, stateRow5_2_0_4, stateRow5_2_0_6, stateRow5_2_0_7, stateRow5_2_0_9, stateRow5_2_0_10, stateRow5_2_0_11]
theorem stateRows_eq5_2_0 : stateRows5_2_0 = final5_2_0.map (List.map Prod.snd) := by
  simp only [stateRows5_2_0, final5_2_0, List.map_cons, List.map_nil, patch_states5_2_0_2, patch_states5_2_0_3, patch_states5_2_0_4, patch_states5_2_0_6, patch_states5_2_0_7, patch_states5_2_0_9, patch_states5_2_0_10, patch_states5_2_0_11]
theorem final_states5_2_0 : final5_2_0 = stateRows5_2_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
