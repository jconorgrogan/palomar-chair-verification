module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart018
public import SpectreFinite.ParentOwnershipFinitePart082
public import SpectreFinite.ParentOwnershipFinitePart113

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_1_3_0 : List State := ParentOwnership.parentRow1811
def patch6_1_3_0 : Patch := literalDomain.zip stateRow6_1_3_0
theorem patch_states6_1_3_0 : patch6_1_3_0.map Prod.snd = stateRow6_1_3_0 := by rfl
def stateRow6_1_3_1 : List State := ParentOwnership.parentRow0294
def patch6_1_3_1 : Patch := literalDomain.zip stateRow6_1_3_1
theorem patch_states6_1_3_1 : patch6_1_3_1.map Prod.snd = stateRow6_1_3_1 := by rfl
def stateRow6_1_3_4 : List State := ParentOwnership.parentRow0291
def patch6_1_3_4 : Patch := literalDomain.zip stateRow6_1_3_4
theorem patch_states6_1_3_4 : patch6_1_3_4.map Prod.snd = stateRow6_1_3_4 := by rfl
def stateRow6_1_3_5 : List State := ParentOwnership.parentRow0300
def patch6_1_3_5 : Patch := literalDomain.zip stateRow6_1_3_5
theorem patch_states6_1_3_5 : patch6_1_3_5.map Prod.snd = stateRow6_1_3_5 := by rfl
def stateRow6_1_3_6 : List State := ParentOwnership.parentRow0289
def patch6_1_3_6 : Patch := literalDomain.zip stateRow6_1_3_6
theorem patch_states6_1_3_6 : patch6_1_3_6.map Prod.snd = stateRow6_1_3_6 := by rfl
def stateRow6_1_3_7 : List State := ParentOwnership.parentRow0292
def patch6_1_3_7 : Patch := literalDomain.zip stateRow6_1_3_7
theorem patch_states6_1_3_7 : patch6_1_3_7.map Prod.snd = stateRow6_1_3_7 := by rfl
def stateRow6_1_3_8 : List State := ParentOwnership.parentRow0290
def patch6_1_3_8 : Patch := literalDomain.zip stateRow6_1_3_8
theorem patch_states6_1_3_8 : patch6_1_3_8.map Prod.snd = stateRow6_1_3_8 := by rfl
def stateRow6_1_3_9 : List State := ParentOwnership.parentRow0293
def patch6_1_3_9 : Patch := literalDomain.zip stateRow6_1_3_9
theorem patch_states6_1_3_9 : patch6_1_3_9.map Prod.snd = stateRow6_1_3_9 := by rfl
def stateRow6_1_3_10 : List State := ParentOwnership.parentRow1325
def patch6_1_3_10 : Patch := literalDomain.zip stateRow6_1_3_10
theorem patch_states6_1_3_10 : patch6_1_3_10.map Prod.snd = stateRow6_1_3_10 := by rfl
def stateRow6_1_3_11 : List State := ParentOwnership.parentRow1326
def patch6_1_3_11 : Patch := literalDomain.zip stateRow6_1_3_11
theorem patch_states6_1_3_11 : patch6_1_3_11.map Prod.snd = stateRow6_1_3_11 := by rfl
def final6_1_3 : List Patch := [patch6_1_3_0, patch6_1_3_1, patch6_1_3_4, patch6_1_3_5, patch6_1_3_6, patch6_1_3_7, patch6_1_3_8, patch6_1_3_9, patch6_1_3_10, patch6_1_3_11]
def stateRows6_1_3 : List (List State) := [stateRow6_1_3_0, stateRow6_1_3_1, stateRow6_1_3_4, stateRow6_1_3_5, stateRow6_1_3_6, stateRow6_1_3_7, stateRow6_1_3_8, stateRow6_1_3_9, stateRow6_1_3_10, stateRow6_1_3_11]
theorem stateRows_eq6_1_3 : stateRows6_1_3 = final6_1_3.map (List.map Prod.snd) := by
  simp only [stateRows6_1_3, final6_1_3, List.map_cons, List.map_nil, patch_states6_1_3_0, patch_states6_1_3_1, patch_states6_1_3_4, patch_states6_1_3_5, patch_states6_1_3_6, patch_states6_1_3_7, patch_states6_1_3_8, patch_states6_1_3_9, patch_states6_1_3_10, patch_states6_1_3_11]
theorem final_states6_1_3 : final6_1_3 = stateRows6_1_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
