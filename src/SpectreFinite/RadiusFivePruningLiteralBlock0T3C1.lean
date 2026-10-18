module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart040
public import SpectreFinite.ParentOwnershipFinitePart083

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_3_1_0 : List State := ParentOwnership.parentRow0641
def patch0_3_1_0 : Patch := literalDomain.zip stateRow0_3_1_0
theorem patch_states0_3_1_0 : patch0_3_1_0.map Prod.snd = stateRow0_3_1_0 := by rfl
def stateRow0_3_1_2 : List State := ParentOwnership.parentRow1329
def patch0_3_1_2 : Patch := literalDomain.zip stateRow0_3_1_2
theorem patch_states0_3_1_2 : patch0_3_1_2.map Prod.snd = stateRow0_3_1_2 := by rfl
def stateRow0_3_1_4 : List State := ParentOwnership.parentRow1330
def patch0_3_1_4 : Patch := literalDomain.zip stateRow0_3_1_4
theorem patch_states0_3_1_4 : patch0_3_1_4.map Prod.snd = stateRow0_3_1_4 := by rfl
def stateRow0_3_1_5 : List State := ParentOwnership.parentRow1334
def patch0_3_1_5 : Patch := literalDomain.zip stateRow0_3_1_5
theorem patch_states0_3_1_5 : patch0_3_1_5.map Prod.snd = stateRow0_3_1_5 := by rfl
def stateRow0_3_1_6 : List State := ParentOwnership.parentRow1331
def patch0_3_1_6 : Patch := literalDomain.zip stateRow0_3_1_6
theorem patch_states0_3_1_6 : patch0_3_1_6.map Prod.snd = stateRow0_3_1_6 := by rfl
def stateRow0_3_1_9 : List State := ParentOwnership.parentRow1332
def patch0_3_1_9 : Patch := literalDomain.zip stateRow0_3_1_9
theorem patch_states0_3_1_9 : patch0_3_1_9.map Prod.snd = stateRow0_3_1_9 := by rfl
def stateRow0_3_1_11 : List State := ParentOwnership.parentRow1333
def patch0_3_1_11 : Patch := literalDomain.zip stateRow0_3_1_11
theorem patch_states0_3_1_11 : patch0_3_1_11.map Prod.snd = stateRow0_3_1_11 := by rfl
def final0_3_1 : List Patch := [patch0_3_1_0, patch0_3_1_2, patch0_3_1_4, patch0_3_1_5, patch0_3_1_6, patch0_3_1_9, patch0_3_1_11]
def stateRows0_3_1 : List (List State) := [stateRow0_3_1_0, stateRow0_3_1_2, stateRow0_3_1_4, stateRow0_3_1_5, stateRow0_3_1_6, stateRow0_3_1_9, stateRow0_3_1_11]
theorem stateRows_eq0_3_1 : stateRows0_3_1 = final0_3_1.map (List.map Prod.snd) := by
  simp only [stateRows0_3_1, final0_3_1, List.map_cons, List.map_nil, patch_states0_3_1_0, patch_states0_3_1_2, patch_states0_3_1_4, patch_states0_3_1_5, patch_states0_3_1_6, patch_states0_3_1_9, patch_states0_3_1_11]
theorem final_states0_3_1 : final0_3_1 = stateRows0_3_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
