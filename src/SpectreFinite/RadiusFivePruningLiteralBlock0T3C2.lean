module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart083
public import SpectreFinite.ParentOwnershipFinitePart084
public import SpectreFinite.ParentOwnershipFinitePart086
public import SpectreFinite.ParentOwnershipFinitePart113

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_3_2_0 : List State := ParentOwnership.parentRow1344
def patch0_3_2_0 : Patch := literalDomain.zip stateRow0_3_2_0
theorem patch_states0_3_2_0 : patch0_3_2_0.map Prod.snd = stateRow0_3_2_0 := by rfl
def stateRow0_3_2_1 : List State := ParentOwnership.parentRow1379
def patch0_3_2_1 : Patch := literalDomain.zip stateRow0_3_2_1
theorem patch_states0_3_2_1 : patch0_3_2_1.map Prod.snd = stateRow0_3_2_1 := by rfl
def stateRow0_3_2_2 : List State := ParentOwnership.parentRow1382
def patch0_3_2_2 : Patch := literalDomain.zip stateRow0_3_2_2
theorem patch_states0_3_2_2 : patch0_3_2_2.map Prod.snd = stateRow0_3_2_2 := by rfl
def stateRow0_3_2_3 : List State := ParentOwnership.parentRow1346
def patch0_3_2_3 : Patch := literalDomain.zip stateRow0_3_2_3
theorem patch_states0_3_2_3 : patch0_3_2_3.map Prod.snd = stateRow0_3_2_3 := by rfl
def stateRow0_3_2_5 : List State := ParentOwnership.parentRow1343
def patch0_3_2_5 : Patch := literalDomain.zip stateRow0_3_2_5
theorem patch_states0_3_2_5 : patch0_3_2_5.map Prod.snd = stateRow0_3_2_5 := by rfl
def stateRow0_3_2_6 : List State := ParentOwnership.parentRow1815
def patch0_3_2_6 : Patch := literalDomain.zip stateRow0_3_2_6
theorem patch_states0_3_2_6 : patch0_3_2_6.map Prod.snd = stateRow0_3_2_6 := by rfl
def stateRow0_3_2_7 : List State := ParentOwnership.parentRow1378
def patch0_3_2_7 : Patch := literalDomain.zip stateRow0_3_2_7
theorem patch_states0_3_2_7 : patch0_3_2_7.map Prod.snd = stateRow0_3_2_7 := by rfl
def stateRow0_3_2_8 : List State := ParentOwnership.parentRow1381
def patch0_3_2_8 : Patch := literalDomain.zip stateRow0_3_2_8
theorem patch_states0_3_2_8 : patch0_3_2_8.map Prod.snd = stateRow0_3_2_8 := by rfl
def stateRow0_3_2_9 : List State := ParentOwnership.parentRow1345
def patch0_3_2_9 : Patch := literalDomain.zip stateRow0_3_2_9
theorem patch_states0_3_2_9 : patch0_3_2_9.map Prod.snd = stateRow0_3_2_9 := by rfl
def stateRow0_3_2_10 : List State := ParentOwnership.parentRow1820
def patch0_3_2_10 : Patch := literalDomain.zip stateRow0_3_2_10
theorem patch_states0_3_2_10 : patch0_3_2_10.map Prod.snd = stateRow0_3_2_10 := by rfl
def final0_3_2 : List Patch := [patch0_3_2_0, patch0_3_2_1, patch0_3_2_2, patch0_3_2_3, patch0_3_2_5, patch0_3_2_6, patch0_3_2_7, patch0_3_2_8, patch0_3_2_9, patch0_3_2_10]
def stateRows0_3_2 : List (List State) := [stateRow0_3_2_0, stateRow0_3_2_1, stateRow0_3_2_2, stateRow0_3_2_3, stateRow0_3_2_5, stateRow0_3_2_6, stateRow0_3_2_7, stateRow0_3_2_8, stateRow0_3_2_9, stateRow0_3_2_10]
theorem stateRows_eq0_3_2 : stateRows0_3_2 = final0_3_2.map (List.map Prod.snd) := by
  simp only [stateRows0_3_2, final0_3_2, List.map_cons, List.map_nil, patch_states0_3_2_0, patch_states0_3_2_1, patch_states0_3_2_2, patch_states0_3_2_3, patch_states0_3_2_5, patch_states0_3_2_6, patch_states0_3_2_7, patch_states0_3_2_8, patch_states0_3_2_9, patch_states0_3_2_10]
theorem final_states0_3_2 : final0_3_2 = stateRows0_3_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
