module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart034
public import SpectreFinite.ParentOwnershipFinitePart035
public import SpectreFinite.ParentOwnershipFinitePart036
public import SpectreFinite.ParentOwnershipFinitePart041

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_4_1_0 : List State := ParentOwnership.parentRow0567
def patch5_4_1_0 : Patch := literalDomain.zip stateRow5_4_1_0
theorem patch_states5_4_1_0 : patch5_4_1_0.map Prod.snd = stateRow5_4_1_0 := by rfl
def stateRow5_4_1_1 : List State := ParentOwnership.parentRow0665
def patch5_4_1_1 : Patch := literalDomain.zip stateRow5_4_1_1
theorem patch_states5_4_1_1 : patch5_4_1_1.map Prod.snd = stateRow5_4_1_1 := by rfl
def stateRow5_4_1_3 : List State := ParentOwnership.parentRow0663
def patch5_4_1_3 : Patch := literalDomain.zip stateRow5_4_1_3
theorem patch_states5_4_1_3 : patch5_4_1_3.map Prod.snd = stateRow5_4_1_3 := by rfl
def stateRow5_4_1_4 : List State := ParentOwnership.parentRow0556
def patch5_4_1_4 : Patch := literalDomain.zip stateRow5_4_1_4
theorem patch_states5_4_1_4 : patch5_4_1_4.map Prod.snd = stateRow5_4_1_4 := by rfl
def stateRow5_4_1_7 : List State := ParentOwnership.parentRow0569
def patch5_4_1_7 : Patch := literalDomain.zip stateRow5_4_1_7
theorem patch_states5_4_1_7 : patch5_4_1_7.map Prod.snd = stateRow5_4_1_7 := by rfl
def stateRow5_4_1_8 : List State := ParentOwnership.parentRow0558
def patch5_4_1_8 : Patch := literalDomain.zip stateRow5_4_1_8
theorem patch_states5_4_1_8 : patch5_4_1_8.map Prod.snd = stateRow5_4_1_8 := by rfl
def stateRow5_4_1_9 : List State := ParentOwnership.parentRow0582
def patch5_4_1_9 : Patch := literalDomain.zip stateRow5_4_1_9
theorem patch_states5_4_1_9 : patch5_4_1_9.map Prod.snd = stateRow5_4_1_9 := by rfl
def stateRow5_4_1_11 : List State := ParentOwnership.parentRow0568
def patch5_4_1_11 : Patch := literalDomain.zip stateRow5_4_1_11
theorem patch_states5_4_1_11 : patch5_4_1_11.map Prod.snd = stateRow5_4_1_11 := by rfl
def final5_4_1 : List Patch := [patch5_4_1_0, patch5_4_1_1, patch5_4_1_3, patch5_4_1_4, patch5_4_1_7, patch5_4_1_8, patch5_4_1_9, patch5_4_1_11]
def stateRows5_4_1 : List (List State) := [stateRow5_4_1_0, stateRow5_4_1_1, stateRow5_4_1_3, stateRow5_4_1_4, stateRow5_4_1_7, stateRow5_4_1_8, stateRow5_4_1_9, stateRow5_4_1_11]
theorem stateRows_eq5_4_1 : stateRows5_4_1 = final5_4_1.map (List.map Prod.snd) := by
  simp only [stateRows5_4_1, final5_4_1, List.map_cons, List.map_nil, patch_states5_4_1_0, patch_states5_4_1_1, patch_states5_4_1_3, patch_states5_4_1_4, patch_states5_4_1_7, patch_states5_4_1_8, patch_states5_4_1_9, patch_states5_4_1_11]
theorem final_states5_4_1 : final5_4_1 = stateRows5_4_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
