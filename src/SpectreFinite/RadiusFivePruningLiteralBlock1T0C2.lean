module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart042
public import SpectreFinite.ParentOwnershipFinitePart120

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_0_2_0 : List State := ParentOwnership.parentRow1926
def patch1_0_2_0 : Patch := literalDomain.zip stateRow1_0_2_0
theorem patch_states1_0_2_0 : patch1_0_2_0.map Prod.snd = stateRow1_0_2_0 := by rfl
def stateRow1_0_2_1 : List State := ParentOwnership.parentRow1927
def patch1_0_2_1 : Patch := literalDomain.zip stateRow1_0_2_1
theorem patch_states1_0_2_1 : patch1_0_2_1.map Prod.snd = stateRow1_0_2_1 := by rfl
def stateRow1_0_2_2 : List State := ParentOwnership.parentRow1928
def patch1_0_2_2 : Patch := literalDomain.zip stateRow1_0_2_2
theorem patch_states1_0_2_2 : patch1_0_2_2.map Prod.snd = stateRow1_0_2_2 := by rfl
def stateRow1_0_2_3 : List State := ParentOwnership.parentRow1929
def patch1_0_2_3 : Patch := literalDomain.zip stateRow1_0_2_3
theorem patch_states1_0_2_3 : patch1_0_2_3.map Prod.snd = stateRow1_0_2_3 := by rfl
def stateRow1_0_2_4 : List State := ParentOwnership.parentRow1930
def patch1_0_2_4 : Patch := literalDomain.zip stateRow1_0_2_4
theorem patch_states1_0_2_4 : patch1_0_2_4.map Prod.snd = stateRow1_0_2_4 := by rfl
def stateRow1_0_2_6 : List State := ParentOwnership.parentRow0681
def patch1_0_2_6 : Patch := literalDomain.zip stateRow1_0_2_6
theorem patch_states1_0_2_6 : patch1_0_2_6.map Prod.snd = stateRow1_0_2_6 := by rfl
def stateRow1_0_2_7 : List State := ParentOwnership.parentRow0682
def patch1_0_2_7 : Patch := literalDomain.zip stateRow1_0_2_7
theorem patch_states1_0_2_7 : patch1_0_2_7.map Prod.snd = stateRow1_0_2_7 := by rfl
def stateRow1_0_2_8 : List State := ParentOwnership.parentRow0683
def patch1_0_2_8 : Patch := literalDomain.zip stateRow1_0_2_8
theorem patch_states1_0_2_8 : patch1_0_2_8.map Prod.snd = stateRow1_0_2_8 := by rfl
def stateRow1_0_2_9 : List State := ParentOwnership.parentRow0684
def patch1_0_2_9 : Patch := literalDomain.zip stateRow1_0_2_9
theorem patch_states1_0_2_9 : patch1_0_2_9.map Prod.snd = stateRow1_0_2_9 := by rfl
def stateRow1_0_2_11 : List State := ParentOwnership.parentRow0685
def patch1_0_2_11 : Patch := literalDomain.zip stateRow1_0_2_11
theorem patch_states1_0_2_11 : patch1_0_2_11.map Prod.snd = stateRow1_0_2_11 := by rfl
def final1_0_2 : List Patch := [patch1_0_2_0, patch1_0_2_1, patch1_0_2_2, patch1_0_2_3, patch1_0_2_4, patch1_0_2_6, patch1_0_2_7, patch1_0_2_8, patch1_0_2_9, patch1_0_2_11]
def stateRows1_0_2 : List (List State) := [stateRow1_0_2_0, stateRow1_0_2_1, stateRow1_0_2_2, stateRow1_0_2_3, stateRow1_0_2_4, stateRow1_0_2_6, stateRow1_0_2_7, stateRow1_0_2_8, stateRow1_0_2_9, stateRow1_0_2_11]
theorem stateRows_eq1_0_2 : stateRows1_0_2 = final1_0_2.map (List.map Prod.snd) := by
  simp only [stateRows1_0_2, final1_0_2, List.map_cons, List.map_nil, patch_states1_0_2_0, patch_states1_0_2_1, patch_states1_0_2_2, patch_states1_0_2_3, patch_states1_0_2_4, patch_states1_0_2_6, patch_states1_0_2_7, patch_states1_0_2_8, patch_states1_0_2_9, patch_states1_0_2_11]
theorem final_states1_0_2 : final1_0_2 = stateRows1_0_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
