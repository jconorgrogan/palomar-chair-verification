module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart045
public import SpectreFinite.ParentOwnershipFinitePart046

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_1_2_0 : List State := ParentOwnership.parentRow0750
def patch5_1_2_0 : Patch := literalDomain.zip stateRow5_1_2_0
theorem patch_states5_1_2_0 : patch5_1_2_0.map Prod.snd = stateRow5_1_2_0 := by rfl
def stateRow5_1_2_1 : List State := ParentOwnership.parentRow0749
def patch5_1_2_1 : Patch := literalDomain.zip stateRow5_1_2_1
theorem patch_states5_1_2_1 : patch5_1_2_1.map Prod.snd = stateRow5_1_2_1 := by rfl
def stateRow5_1_2_2 : List State := ParentOwnership.parentRow0740
def patch5_1_2_2 : Patch := literalDomain.zip stateRow5_1_2_2
theorem patch_states5_1_2_2 : patch5_1_2_2.map Prod.snd = stateRow5_1_2_2 := by rfl
def stateRow5_1_2_3 : List State := ParentOwnership.parentRow0742
def patch5_1_2_3 : Patch := literalDomain.zip stateRow5_1_2_3
theorem patch_states5_1_2_3 : patch5_1_2_3.map Prod.snd = stateRow5_1_2_3 := by rfl
def stateRow5_1_2_4 : List State := ParentOwnership.parentRow0739
def patch5_1_2_4 : Patch := literalDomain.zip stateRow5_1_2_4
theorem patch_states5_1_2_4 : patch5_1_2_4.map Prod.snd = stateRow5_1_2_4 := by rfl
def stateRow5_1_2_5 : List State := ParentOwnership.parentRow0741
def patch5_1_2_5 : Patch := literalDomain.zip stateRow5_1_2_5
theorem patch_states5_1_2_5 : patch5_1_2_5.map Prod.snd = stateRow5_1_2_5 := by rfl
def stateRow5_1_2_6 : List State := ParentOwnership.parentRow0727
def patch5_1_2_6 : Patch := literalDomain.zip stateRow5_1_2_6
theorem patch_states5_1_2_6 : patch5_1_2_6.map Prod.snd = stateRow5_1_2_6 := by rfl
def stateRow5_1_2_7 : List State := ParentOwnership.parentRow0729
def patch5_1_2_7 : Patch := literalDomain.zip stateRow5_1_2_7
theorem patch_states5_1_2_7 : patch5_1_2_7.map Prod.snd = stateRow5_1_2_7 := by rfl
def stateRow5_1_2_8 : List State := ParentOwnership.parentRow0726
def patch5_1_2_8 : Patch := literalDomain.zip stateRow5_1_2_8
theorem patch_states5_1_2_8 : patch5_1_2_8.map Prod.snd = stateRow5_1_2_8 := by rfl
def stateRow5_1_2_9 : List State := ParentOwnership.parentRow0728
def patch5_1_2_9 : Patch := literalDomain.zip stateRow5_1_2_9
theorem patch_states5_1_2_9 : patch5_1_2_9.map Prod.snd = stateRow5_1_2_9 := by rfl
def stateRow5_1_2_10 : List State := ParentOwnership.parentRow0738
def patch5_1_2_10 : Patch := literalDomain.zip stateRow5_1_2_10
theorem patch_states5_1_2_10 : patch5_1_2_10.map Prod.snd = stateRow5_1_2_10 := by rfl
def final5_1_2 : List Patch := [patch5_1_2_0, patch5_1_2_1, patch5_1_2_2, patch5_1_2_3, patch5_1_2_4, patch5_1_2_5, patch5_1_2_6, patch5_1_2_7, patch5_1_2_8, patch5_1_2_9, patch5_1_2_10]
def stateRows5_1_2 : List (List State) := [stateRow5_1_2_0, stateRow5_1_2_1, stateRow5_1_2_2, stateRow5_1_2_3, stateRow5_1_2_4, stateRow5_1_2_5, stateRow5_1_2_6, stateRow5_1_2_7, stateRow5_1_2_8, stateRow5_1_2_9, stateRow5_1_2_10]
theorem stateRows_eq5_1_2 : stateRows5_1_2 = final5_1_2.map (List.map Prod.snd) := by
  simp only [stateRows5_1_2, final5_1_2, List.map_cons, List.map_nil, patch_states5_1_2_0, patch_states5_1_2_1, patch_states5_1_2_2, patch_states5_1_2_3, patch_states5_1_2_4, patch_states5_1_2_5, patch_states5_1_2_6, patch_states5_1_2_7, patch_states5_1_2_8, patch_states5_1_2_9, patch_states5_1_2_10]
theorem final_states5_1_2 : final5_1_2 = stateRows5_1_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
