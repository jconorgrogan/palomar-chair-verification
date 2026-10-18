module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart105
public import SpectreFinite.ParentOwnershipFinitePart106
public import SpectreFinite.ParentOwnershipFinitePart107

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_1_3_0 : List State := ParentOwnership.parentRow1682
def patch0_1_3_0 : Patch := literalDomain.zip stateRow0_1_3_0
theorem patch_states0_1_3_0 : patch0_1_3_0.map Prod.snd = stateRow0_1_3_0 := by rfl
def stateRow0_1_3_2 : List State := ParentOwnership.parentRow1708
def patch0_1_3_2 : Patch := literalDomain.zip stateRow0_1_3_2
theorem patch_states0_1_3_2 : patch0_1_3_2.map Prod.snd = stateRow0_1_3_2 := by rfl
def stateRow0_1_3_3 : List State := ParentOwnership.parentRow1693
def patch0_1_3_3 : Patch := literalDomain.zip stateRow0_1_3_3
theorem patch_states0_1_3_3 : patch0_1_3_3.map Prod.snd = stateRow0_1_3_3 := by rfl
def stateRow0_1_3_4 : List State := ParentOwnership.parentRow1710
def patch0_1_3_4 : Patch := literalDomain.zip stateRow0_1_3_4
theorem patch_states0_1_3_4 : patch0_1_3_4.map Prod.snd = stateRow0_1_3_4 := by rfl
def stateRow0_1_3_5 : List State := ParentOwnership.parentRow1709
def patch0_1_3_5 : Patch := literalDomain.zip stateRow0_1_3_5
theorem patch_states0_1_3_5 : patch0_1_3_5.map Prod.snd = stateRow0_1_3_5 := by rfl
def stateRow0_1_3_6 : List State := ParentOwnership.parentRow1712
def patch0_1_3_6 : Patch := literalDomain.zip stateRow0_1_3_6
theorem patch_states0_1_3_6 : patch0_1_3_6.map Prod.snd = stateRow0_1_3_6 := by rfl
def stateRow0_1_3_8 : List State := ParentOwnership.parentRow1703
def patch0_1_3_8 : Patch := literalDomain.zip stateRow0_1_3_8
theorem patch_states0_1_3_8 : patch0_1_3_8.map Prod.snd = stateRow0_1_3_8 := by rfl
def stateRow0_1_3_9 : List State := ParentOwnership.parentRow1691
def patch0_1_3_9 : Patch := literalDomain.zip stateRow0_1_3_9
theorem patch_states0_1_3_9 : patch0_1_3_9.map Prod.snd = stateRow0_1_3_9 := by rfl
def stateRow0_1_3_11 : List State := ParentOwnership.parentRow1699
def patch0_1_3_11 : Patch := literalDomain.zip stateRow0_1_3_11
theorem patch_states0_1_3_11 : patch0_1_3_11.map Prod.snd = stateRow0_1_3_11 := by rfl
def final0_1_3 : List Patch := [patch0_1_3_0, patch0_1_3_2, patch0_1_3_3, patch0_1_3_4, patch0_1_3_5, patch0_1_3_6, patch0_1_3_8, patch0_1_3_9, patch0_1_3_11]
def stateRows0_1_3 : List (List State) := [stateRow0_1_3_0, stateRow0_1_3_2, stateRow0_1_3_3, stateRow0_1_3_4, stateRow0_1_3_5, stateRow0_1_3_6, stateRow0_1_3_8, stateRow0_1_3_9, stateRow0_1_3_11]
theorem stateRows_eq0_1_3 : stateRows0_1_3 = final0_1_3.map (List.map Prod.snd) := by
  simp only [stateRows0_1_3, final0_1_3, List.map_cons, List.map_nil, patch_states0_1_3_0, patch_states0_1_3_2, patch_states0_1_3_3, patch_states0_1_3_4, patch_states0_1_3_5, patch_states0_1_3_6, patch_states0_1_3_8, patch_states0_1_3_9, patch_states0_1_3_11]
theorem final_states0_1_3 : final0_1_3 = stateRows0_1_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
