module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart004
public import SpectreFinite.ParentOwnershipFinitePart080

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_0_0_0 : List State := ParentOwnership.parentRow0064
def patch0_0_0_0 : Patch := literalDomain.zip stateRow0_0_0_0
theorem patch_states0_0_0_0 : patch0_0_0_0.map Prod.snd = stateRow0_0_0_0 := by rfl
def stateRow0_0_0_1 : List State := ParentOwnership.parentRow0065
def patch0_0_0_1 : Patch := literalDomain.zip stateRow0_0_0_1
theorem patch_states0_0_0_1 : patch0_0_0_1.map Prod.snd = stateRow0_0_0_1 := by rfl
def stateRow0_0_0_3 : List State := ParentOwnership.parentRow0070
def patch0_0_0_3 : Patch := literalDomain.zip stateRow0_0_0_3
theorem patch_states0_0_0_3 : patch0_0_0_3.map Prod.snd = stateRow0_0_0_3 := by rfl
def stateRow0_0_0_4 : List State := ParentOwnership.parentRow0071
def patch0_0_0_4 : Patch := literalDomain.zip stateRow0_0_0_4
theorem patch_states0_0_0_4 : patch0_0_0_4.map Prod.snd = stateRow0_0_0_4 := by rfl
def stateRow0_0_0_5 : List State := ParentOwnership.parentRow0072
def patch0_0_0_5 : Patch := literalDomain.zip stateRow0_0_0_5
theorem patch_states0_0_0_5 : patch0_0_0_5.map Prod.snd = stateRow0_0_0_5 := by rfl
def stateRow0_0_0_6 : List State := ParentOwnership.parentRow1285
def patch0_0_0_6 : Patch := literalDomain.zip stateRow0_0_0_6
theorem patch_states0_0_0_6 : patch0_0_0_6.map Prod.snd = stateRow0_0_0_6 := by rfl
def stateRow0_0_0_8 : List State := ParentOwnership.parentRow1287
def patch0_0_0_8 : Patch := literalDomain.zip stateRow0_0_0_8
theorem patch_states0_0_0_8 : patch0_0_0_8.map Prod.snd = stateRow0_0_0_8 := by rfl
def stateRow0_0_0_9 : List State := ParentOwnership.parentRow1288
def patch0_0_0_9 : Patch := literalDomain.zip stateRow0_0_0_9
theorem patch_states0_0_0_9 : patch0_0_0_9.map Prod.snd = stateRow0_0_0_9 := by rfl
def stateRow0_0_0_10 : List State := ParentOwnership.parentRow1289
def patch0_0_0_10 : Patch := literalDomain.zip stateRow0_0_0_10
theorem patch_states0_0_0_10 : patch0_0_0_10.map Prod.snd = stateRow0_0_0_10 := by rfl
def stateRow0_0_0_11 : List State := ParentOwnership.parentRow1290
def patch0_0_0_11 : Patch := literalDomain.zip stateRow0_0_0_11
theorem patch_states0_0_0_11 : patch0_0_0_11.map Prod.snd = stateRow0_0_0_11 := by rfl
def final0_0_0 : List Patch := [patch0_0_0_0, patch0_0_0_1, patch0_0_0_3, patch0_0_0_4, patch0_0_0_5, patch0_0_0_6, patch0_0_0_8, patch0_0_0_9, patch0_0_0_10, patch0_0_0_11]
def stateRows0_0_0 : List (List State) := [stateRow0_0_0_0, stateRow0_0_0_1, stateRow0_0_0_3, stateRow0_0_0_4, stateRow0_0_0_5, stateRow0_0_0_6, stateRow0_0_0_8, stateRow0_0_0_9, stateRow0_0_0_10, stateRow0_0_0_11]
theorem stateRows_eq0_0_0 : stateRows0_0_0 = final0_0_0.map (List.map Prod.snd) := by
  simp only [stateRows0_0_0, final0_0_0, List.map_cons, List.map_nil, patch_states0_0_0_0, patch_states0_0_0_1, patch_states0_0_0_3, patch_states0_0_0_4, patch_states0_0_0_5, patch_states0_0_0_6, patch_states0_0_0_8, patch_states0_0_0_9, patch_states0_0_0_10, patch_states0_0_0_11]
theorem final_states0_0_0 : final0_0_0 = stateRows0_0_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
