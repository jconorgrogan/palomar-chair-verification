module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart051
public import SpectreFinite.ParentOwnershipFinitePart052
public import SpectreFinite.ParentOwnershipFinitePart053
public import SpectreFinite.ParentOwnershipFinitePart057

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_1_3_0 : List State := ParentOwnership.parentRow0843
def patch1_1_3_0 : Patch := literalDomain.zip stateRow1_1_3_0
theorem patch_states1_1_3_0 : patch1_1_3_0.map Prod.snd = stateRow1_1_3_0 := by rfl
def stateRow1_1_3_1 : List State := ParentOwnership.parentRow0844
def patch1_1_3_1 : Patch := literalDomain.zip stateRow1_1_3_1
theorem patch_states1_1_3_1 : patch1_1_3_1.map Prod.snd = stateRow1_1_3_1 := by rfl
def stateRow1_1_3_3 : List State := ParentOwnership.parentRow0827
def patch1_1_3_3 : Patch := literalDomain.zip stateRow1_1_3_3
theorem patch_states1_1_3_3 : patch1_1_3_3.map Prod.snd = stateRow1_1_3_3 := by rfl
def stateRow1_1_3_5 : List State := ParentOwnership.parentRow0835
def patch1_1_3_5 : Patch := literalDomain.zip stateRow1_1_3_5
theorem patch_states1_1_3_5 : patch1_1_3_5.map Prod.snd = stateRow1_1_3_5 := by rfl
def stateRow1_1_3_6 : List State := ParentOwnership.parentRow0836
def patch1_1_3_6 : Patch := literalDomain.zip stateRow1_1_3_6
theorem patch_states1_1_3_6 : patch1_1_3_6.map Prod.snd = stateRow1_1_3_6 := by rfl
def stateRow1_1_3_7 : List State := ParentOwnership.parentRow0847
def patch1_1_3_7 : Patch := literalDomain.zip stateRow1_1_3_7
theorem patch_states1_1_3_7 : patch1_1_3_7.map Prod.snd = stateRow1_1_3_7 := by rfl
def stateRow1_1_3_8 : List State := ParentOwnership.parentRow0846
def patch1_1_3_8 : Patch := literalDomain.zip stateRow1_1_3_8
theorem patch_states1_1_3_8 : patch1_1_3_8.map Prod.snd = stateRow1_1_3_8 := by rfl
def stateRow1_1_3_9 : List State := ParentOwnership.parentRow0848
def patch1_1_3_9 : Patch := literalDomain.zip stateRow1_1_3_9
theorem patch_states1_1_3_9 : patch1_1_3_9.map Prod.snd = stateRow1_1_3_9 := by rfl
def stateRow1_1_3_10 : List State := ParentOwnership.parentRow0919
def patch1_1_3_10 : Patch := literalDomain.zip stateRow1_1_3_10
theorem patch_states1_1_3_10 : patch1_1_3_10.map Prod.snd = stateRow1_1_3_10 := by rfl
def stateRow1_1_3_11 : List State := ParentOwnership.parentRow0830
def patch1_1_3_11 : Patch := literalDomain.zip stateRow1_1_3_11
theorem patch_states1_1_3_11 : patch1_1_3_11.map Prod.snd = stateRow1_1_3_11 := by rfl
def final1_1_3 : List Patch := [patch1_1_3_0, patch1_1_3_1, patch1_1_3_3, patch1_1_3_5, patch1_1_3_6, patch1_1_3_7, patch1_1_3_8, patch1_1_3_9, patch1_1_3_10, patch1_1_3_11]
def stateRows1_1_3 : List (List State) := [stateRow1_1_3_0, stateRow1_1_3_1, stateRow1_1_3_3, stateRow1_1_3_5, stateRow1_1_3_6, stateRow1_1_3_7, stateRow1_1_3_8, stateRow1_1_3_9, stateRow1_1_3_10, stateRow1_1_3_11]
theorem stateRows_eq1_1_3 : stateRows1_1_3 = final1_1_3.map (List.map Prod.snd) := by
  simp only [stateRows1_1_3, final1_1_3, List.map_cons, List.map_nil, patch_states1_1_3_0, patch_states1_1_3_1, patch_states1_1_3_3, patch_states1_1_3_5, patch_states1_1_3_6, patch_states1_1_3_7, patch_states1_1_3_8, patch_states1_1_3_9, patch_states1_1_3_10, patch_states1_1_3_11]
theorem final_states1_1_3 : final1_1_3 = stateRows1_1_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
