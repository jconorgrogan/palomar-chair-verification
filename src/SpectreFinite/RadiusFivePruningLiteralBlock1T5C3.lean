module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart055
public import SpectreFinite.ParentOwnershipFinitePart056
public import SpectreFinite.ParentOwnershipFinitePart063
public import SpectreFinite.ParentOwnershipFinitePart064

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_5_3_0 : List State := ParentOwnership.parentRow1026
def patch1_5_3_0 : Patch := literalDomain.zip stateRow1_5_3_0
theorem patch_states1_5_3_0 : patch1_5_3_0.map Prod.snd = stateRow1_5_3_0 := by rfl
def stateRow1_5_3_1 : List State := ParentOwnership.parentRow1020
def patch1_5_3_1 : Patch := literalDomain.zip stateRow1_5_3_1
theorem patch_states1_5_3_1 : patch1_5_3_1.map Prod.snd = stateRow1_5_3_1 := by rfl
def stateRow1_5_3_3 : List State := ParentOwnership.parentRow0892
def patch1_5_3_3 : Patch := literalDomain.zip stateRow1_5_3_3
theorem patch_states1_5_3_3 : patch1_5_3_3.map Prod.snd = stateRow1_5_3_3 := by rfl
def stateRow1_5_3_5 : List State := ParentOwnership.parentRow0893
def patch1_5_3_5 : Patch := literalDomain.zip stateRow1_5_3_5
theorem patch_states1_5_3_5 : patch1_5_3_5.map Prod.snd = stateRow1_5_3_5 := by rfl
def stateRow1_5_3_6 : List State := ParentOwnership.parentRow0890
def patch1_5_3_6 : Patch := literalDomain.zip stateRow1_5_3_6
theorem patch_states1_5_3_6 : patch1_5_3_6.map Prod.snd = stateRow1_5_3_6 := by rfl
def stateRow1_5_3_7 : List State := ParentOwnership.parentRow1027
def patch1_5_3_7 : Patch := literalDomain.zip stateRow1_5_3_7
theorem patch_states1_5_3_7 : patch1_5_3_7.map Prod.snd = stateRow1_5_3_7 := by rfl
def stateRow1_5_3_8 : List State := ParentOwnership.parentRow0894
def patch1_5_3_8 : Patch := literalDomain.zip stateRow1_5_3_8
theorem patch_states1_5_3_8 : patch1_5_3_8.map Prod.snd = stateRow1_5_3_8 := by rfl
def stateRow1_5_3_9 : List State := ParentOwnership.parentRow0891
def patch1_5_3_9 : Patch := literalDomain.zip stateRow1_5_3_9
theorem patch_states1_5_3_9 : patch1_5_3_9.map Prod.snd = stateRow1_5_3_9 := by rfl
def stateRow1_5_3_10 : List State := ParentOwnership.parentRow0895
def patch1_5_3_10 : Patch := literalDomain.zip stateRow1_5_3_10
theorem patch_states1_5_3_10 : patch1_5_3_10.map Prod.snd = stateRow1_5_3_10 := by rfl
def stateRow1_5_3_11 : List State := ParentOwnership.parentRow0897
def patch1_5_3_11 : Patch := literalDomain.zip stateRow1_5_3_11
theorem patch_states1_5_3_11 : patch1_5_3_11.map Prod.snd = stateRow1_5_3_11 := by rfl
def final1_5_3 : List Patch := [patch1_5_3_0, patch1_5_3_1, patch1_5_3_3, patch1_5_3_5, patch1_5_3_6, patch1_5_3_7, patch1_5_3_8, patch1_5_3_9, patch1_5_3_10, patch1_5_3_11]
def stateRows1_5_3 : List (List State) := [stateRow1_5_3_0, stateRow1_5_3_1, stateRow1_5_3_3, stateRow1_5_3_5, stateRow1_5_3_6, stateRow1_5_3_7, stateRow1_5_3_8, stateRow1_5_3_9, stateRow1_5_3_10, stateRow1_5_3_11]
theorem stateRows_eq1_5_3 : stateRows1_5_3 = final1_5_3.map (List.map Prod.snd) := by
  simp only [stateRows1_5_3, final1_5_3, List.map_cons, List.map_nil, patch_states1_5_3_0, patch_states1_5_3_1, patch_states1_5_3_3, patch_states1_5_3_5, patch_states1_5_3_6, patch_states1_5_3_7, patch_states1_5_3_8, patch_states1_5_3_9, patch_states1_5_3_10, patch_states1_5_3_11]
theorem final_states1_5_3 : final1_5_3 = stateRows1_5_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
