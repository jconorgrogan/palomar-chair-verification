module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart101

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_0_1_0 : List State := ParentOwnership.parentRow1616
def patch5_0_1_0 : Patch := literalDomain.zip stateRow5_0_1_0
theorem patch_states5_0_1_0 : patch5_0_1_0.map Prod.snd = stateRow5_0_1_0 := by rfl
def stateRow5_0_1_1 : List State := ParentOwnership.parentRow1617
def patch5_0_1_1 : Patch := literalDomain.zip stateRow5_0_1_1
theorem patch_states5_0_1_1 : patch5_0_1_1.map Prod.snd = stateRow5_0_1_1 := by rfl
def stateRow5_0_1_3 : List State := ParentOwnership.parentRow1618
def patch5_0_1_3 : Patch := literalDomain.zip stateRow5_0_1_3
theorem patch_states5_0_1_3 : patch5_0_1_3.map Prod.snd = stateRow5_0_1_3 := by rfl
def stateRow5_0_1_4 : List State := ParentOwnership.parentRow1619
def patch5_0_1_4 : Patch := literalDomain.zip stateRow5_0_1_4
theorem patch_states5_0_1_4 : patch5_0_1_4.map Prod.snd = stateRow5_0_1_4 := by rfl
def stateRow5_0_1_7 : List State := ParentOwnership.parentRow1620
def patch5_0_1_7 : Patch := literalDomain.zip stateRow5_0_1_7
theorem patch_states5_0_1_7 : patch5_0_1_7.map Prod.snd = stateRow5_0_1_7 := by rfl
def stateRow5_0_1_8 : List State := ParentOwnership.parentRow1621
def patch5_0_1_8 : Patch := literalDomain.zip stateRow5_0_1_8
theorem patch_states5_0_1_8 : patch5_0_1_8.map Prod.snd = stateRow5_0_1_8 := by rfl
def stateRow5_0_1_9 : List State := ParentOwnership.parentRow1622
def patch5_0_1_9 : Patch := literalDomain.zip stateRow5_0_1_9
theorem patch_states5_0_1_9 : patch5_0_1_9.map Prod.snd = stateRow5_0_1_9 := by rfl
def stateRow5_0_1_11 : List State := ParentOwnership.parentRow1623
def patch5_0_1_11 : Patch := literalDomain.zip stateRow5_0_1_11
theorem patch_states5_0_1_11 : patch5_0_1_11.map Prod.snd = stateRow5_0_1_11 := by rfl
def final5_0_1 : List Patch := [patch5_0_1_0, patch5_0_1_1, patch5_0_1_3, patch5_0_1_4, patch5_0_1_7, patch5_0_1_8, patch5_0_1_9, patch5_0_1_11]
def stateRows5_0_1 : List (List State) := [stateRow5_0_1_0, stateRow5_0_1_1, stateRow5_0_1_3, stateRow5_0_1_4, stateRow5_0_1_7, stateRow5_0_1_8, stateRow5_0_1_9, stateRow5_0_1_11]
theorem stateRows_eq5_0_1 : stateRows5_0_1 = final5_0_1.map (List.map Prod.snd) := by
  simp only [stateRows5_0_1, final5_0_1, List.map_cons, List.map_nil, patch_states5_0_1_0, patch_states5_0_1_1, patch_states5_0_1_3, patch_states5_0_1_4, patch_states5_0_1_7, patch_states5_0_1_8, patch_states5_0_1_9, patch_states5_0_1_11]
theorem final_states5_0_1 : final5_0_1 = stateRows5_0_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
