module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart020
public import SpectreFinite.ParentOwnershipFinitePart021
public import SpectreFinite.ParentOwnershipFinitePart022
public import SpectreFinite.ParentOwnershipFinitePart090

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_2_1_1 : List State := ParentOwnership.parentRow0339
def patch1_2_1_1 : Patch := literalDomain.zip stateRow1_2_1_1
theorem patch_states1_2_1_1 : patch1_2_1_1.map Prod.snd = stateRow1_2_1_1 := by rfl
def stateRow1_2_1_2 : List State := ParentOwnership.parentRow0343
def patch1_2_1_2 : Patch := literalDomain.zip stateRow1_2_1_2
theorem patch_states1_2_1_2 : patch1_2_1_2.map Prod.snd = stateRow1_2_1_2 := by rfl
def stateRow1_2_1_3 : List State := ParentOwnership.parentRow0341
def patch1_2_1_3 : Patch := literalDomain.zip stateRow1_2_1_3
theorem patch_states1_2_1_3 : patch1_2_1_3.map Prod.snd = stateRow1_2_1_3 := by rfl
def stateRow1_2_1_4 : List State := ParentOwnership.parentRow0345
def patch1_2_1_4 : Patch := literalDomain.zip stateRow1_2_1_4
theorem patch_states1_2_1_4 : patch1_2_1_4.map Prod.snd = stateRow1_2_1_4 := by rfl
def stateRow1_2_1_5 : List State := ParentOwnership.parentRow0358
def patch1_2_1_5 : Patch := literalDomain.zip stateRow1_2_1_5
theorem patch_states1_2_1_5 : patch1_2_1_5.map Prod.snd = stateRow1_2_1_5 := by rfl
def stateRow1_2_1_6 : List State := ParentOwnership.parentRow0334
def patch1_2_1_6 : Patch := literalDomain.zip stateRow1_2_1_6
theorem patch_states1_2_1_6 : patch1_2_1_6.map Prod.snd = stateRow1_2_1_6 := by rfl
def stateRow1_2_1_8 : List State := ParentOwnership.parentRow0337
def patch1_2_1_8 : Patch := literalDomain.zip stateRow1_2_1_8
theorem patch_states1_2_1_8 : patch1_2_1_8.map Prod.snd = stateRow1_2_1_8 := by rfl
def stateRow1_2_1_9 : List State := ParentOwnership.parentRow1454
def patch1_2_1_9 : Patch := literalDomain.zip stateRow1_2_1_9
theorem patch_states1_2_1_9 : patch1_2_1_9.map Prod.snd = stateRow1_2_1_9 := by rfl
def stateRow1_2_1_10 : List State := ParentOwnership.parentRow1450
def patch1_2_1_10 : Patch := literalDomain.zip stateRow1_2_1_10
theorem patch_states1_2_1_10 : patch1_2_1_10.map Prod.snd = stateRow1_2_1_10 := by rfl
def final1_2_1 : List Patch := [patch1_2_1_1, patch1_2_1_2, patch1_2_1_3, patch1_2_1_4, patch1_2_1_5, patch1_2_1_6, patch1_2_1_8, patch1_2_1_9, patch1_2_1_10]
def stateRows1_2_1 : List (List State) := [stateRow1_2_1_1, stateRow1_2_1_2, stateRow1_2_1_3, stateRow1_2_1_4, stateRow1_2_1_5, stateRow1_2_1_6, stateRow1_2_1_8, stateRow1_2_1_9, stateRow1_2_1_10]
theorem stateRows_eq1_2_1 : stateRows1_2_1 = final1_2_1.map (List.map Prod.snd) := by
  simp only [stateRows1_2_1, final1_2_1, List.map_cons, List.map_nil, patch_states1_2_1_1, patch_states1_2_1_2, patch_states1_2_1_3, patch_states1_2_1_4, patch_states1_2_1_5, patch_states1_2_1_6, patch_states1_2_1_8, patch_states1_2_1_9, patch_states1_2_1_10]
theorem final_states1_2_1 : final1_2_1 = stateRows1_2_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
