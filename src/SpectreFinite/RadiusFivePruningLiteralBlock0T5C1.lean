module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart019
public import SpectreFinite.ParentOwnershipFinitePart066
public import SpectreFinite.ParentOwnershipFinitePart067
public import SpectreFinite.ParentOwnershipFinitePart068

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_5_1_0 : List State := ParentOwnership.parentRow1103
def patch0_5_1_0 : Patch := literalDomain.zip stateRow0_5_1_0
theorem patch_states0_5_1_0 : patch0_5_1_0.map Prod.snd = stateRow0_5_1_0 := by rfl
def stateRow0_5_1_2 : List State := ParentOwnership.parentRow1067
def patch0_5_1_2 : Patch := literalDomain.zip stateRow0_5_1_2
theorem patch_states0_5_1_2 : patch0_5_1_2.map Prod.snd = stateRow0_5_1_2 := by rfl
def stateRow0_5_1_4 : List State := ParentOwnership.parentRow1059
def patch0_5_1_4 : Patch := literalDomain.zip stateRow0_5_1_4
theorem patch_states0_5_1_4 : patch0_5_1_4.map Prod.snd = stateRow0_5_1_4 := by rfl
def stateRow0_5_1_5 : List State := ParentOwnership.parentRow0311
def patch0_5_1_5 : Patch := literalDomain.zip stateRow0_5_1_5
theorem patch_states0_5_1_5 : patch0_5_1_5.map Prod.snd = stateRow0_5_1_5 := by rfl
def stateRow0_5_1_6 : List State := ParentOwnership.parentRow0310
def patch0_5_1_6 : Patch := literalDomain.zip stateRow0_5_1_6
theorem patch_states0_5_1_6 : patch0_5_1_6.map Prod.snd = stateRow0_5_1_6 := by rfl
def stateRow0_5_1_9 : List State := ParentOwnership.parentRow1076
def patch0_5_1_9 : Patch := literalDomain.zip stateRow0_5_1_9
theorem patch_states0_5_1_9 : patch0_5_1_9.map Prod.snd = stateRow0_5_1_9 := by rfl
def stateRow0_5_1_11 : List State := ParentOwnership.parentRow1077
def patch0_5_1_11 : Patch := literalDomain.zip stateRow0_5_1_11
theorem patch_states0_5_1_11 : patch0_5_1_11.map Prod.snd = stateRow0_5_1_11 := by rfl
def final0_5_1 : List Patch := [patch0_5_1_0, patch0_5_1_2, patch0_5_1_4, patch0_5_1_5, patch0_5_1_6, patch0_5_1_9, patch0_5_1_11]
def stateRows0_5_1 : List (List State) := [stateRow0_5_1_0, stateRow0_5_1_2, stateRow0_5_1_4, stateRow0_5_1_5, stateRow0_5_1_6, stateRow0_5_1_9, stateRow0_5_1_11]
theorem stateRows_eq0_5_1 : stateRows0_5_1 = final0_5_1.map (List.map Prod.snd) := by
  simp only [stateRows0_5_1, final0_5_1, List.map_cons, List.map_nil, patch_states0_5_1_0, patch_states0_5_1_2, patch_states0_5_1_4, patch_states0_5_1_5, patch_states0_5_1_6, patch_states0_5_1_9, patch_states0_5_1_11]
theorem final_states0_5_1 : final0_5_1 = stateRows0_5_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
