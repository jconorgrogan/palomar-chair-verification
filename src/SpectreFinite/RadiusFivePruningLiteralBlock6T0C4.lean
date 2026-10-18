module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart084
public import SpectreFinite.ParentOwnershipFinitePart085

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_0_4_0 : List State := ParentOwnership.parentRow1357
def patch6_0_4_0 : Patch := literalDomain.zip stateRow6_0_4_0
theorem patch_states6_0_4_0 : patch6_0_4_0.map Prod.snd = stateRow6_0_4_0 := by rfl
def stateRow6_0_4_1 : List State := ParentOwnership.parentRow1358
def patch6_0_4_1 : Patch := literalDomain.zip stateRow6_0_4_1
theorem patch_states6_0_4_1 : patch6_0_4_1.map Prod.snd = stateRow6_0_4_1 := by rfl
def stateRow6_0_4_2 : List State := ParentOwnership.parentRow1359
def patch6_0_4_2 : Patch := literalDomain.zip stateRow6_0_4_2
theorem patch_states6_0_4_2 : patch6_0_4_2.map Prod.snd = stateRow6_0_4_2 := by rfl
def stateRow6_0_4_3 : List State := ParentOwnership.parentRow1366
def patch6_0_4_3 : Patch := literalDomain.zip stateRow6_0_4_3
theorem patch_states6_0_4_3 : patch6_0_4_3.map Prod.snd = stateRow6_0_4_3 := by rfl
def stateRow6_0_4_4 : List State := ParentOwnership.parentRow1367
def patch6_0_4_4 : Patch := literalDomain.zip stateRow6_0_4_4
theorem patch_states6_0_4_4 : patch6_0_4_4.map Prod.snd = stateRow6_0_4_4 := by rfl
def stateRow6_0_4_5 : List State := ParentOwnership.parentRow1368
def patch6_0_4_5 : Patch := literalDomain.zip stateRow6_0_4_5
theorem patch_states6_0_4_5 : patch6_0_4_5.map Prod.snd = stateRow6_0_4_5 := by rfl
def stateRow6_0_4_6 : List State := ParentOwnership.parentRow1369
def patch6_0_4_6 : Patch := literalDomain.zip stateRow6_0_4_6
theorem patch_states6_0_4_6 : patch6_0_4_6.map Prod.snd = stateRow6_0_4_6 := by rfl
def stateRow6_0_4_7 : List State := ParentOwnership.parentRow1370
def patch6_0_4_7 : Patch := literalDomain.zip stateRow6_0_4_7
theorem patch_states6_0_4_7 : patch6_0_4_7.map Prod.snd = stateRow6_0_4_7 := by rfl
def stateRow6_0_4_8 : List State := ParentOwnership.parentRow1371
def patch6_0_4_8 : Patch := literalDomain.zip stateRow6_0_4_8
theorem patch_states6_0_4_8 : patch6_0_4_8.map Prod.snd = stateRow6_0_4_8 := by rfl
def stateRow6_0_4_9 : List State := ParentOwnership.parentRow1372
def patch6_0_4_9 : Patch := literalDomain.zip stateRow6_0_4_9
theorem patch_states6_0_4_9 : patch6_0_4_9.map Prod.snd = stateRow6_0_4_9 := by rfl
def stateRow6_0_4_10 : List State := ParentOwnership.parentRow1373
def patch6_0_4_10 : Patch := literalDomain.zip stateRow6_0_4_10
theorem patch_states6_0_4_10 : patch6_0_4_10.map Prod.snd = stateRow6_0_4_10 := by rfl
def stateRow6_0_4_11 : List State := ParentOwnership.parentRow1374
def patch6_0_4_11 : Patch := literalDomain.zip stateRow6_0_4_11
theorem patch_states6_0_4_11 : patch6_0_4_11.map Prod.snd = stateRow6_0_4_11 := by rfl
def final6_0_4 : List Patch := [patch6_0_4_0, patch6_0_4_1, patch6_0_4_2, patch6_0_4_3, patch6_0_4_4, patch6_0_4_5, patch6_0_4_6, patch6_0_4_7, patch6_0_4_8, patch6_0_4_9, patch6_0_4_10, patch6_0_4_11]
def stateRows6_0_4 : List (List State) := [stateRow6_0_4_0, stateRow6_0_4_1, stateRow6_0_4_2, stateRow6_0_4_3, stateRow6_0_4_4, stateRow6_0_4_5, stateRow6_0_4_6, stateRow6_0_4_7, stateRow6_0_4_8, stateRow6_0_4_9, stateRow6_0_4_10, stateRow6_0_4_11]
theorem stateRows_eq6_0_4 : stateRows6_0_4 = final6_0_4.map (List.map Prod.snd) := by
  simp only [stateRows6_0_4, final6_0_4, List.map_cons, List.map_nil, patch_states6_0_4_0, patch_states6_0_4_1, patch_states6_0_4_2, patch_states6_0_4_3, patch_states6_0_4_4, patch_states6_0_4_5, patch_states6_0_4_6, patch_states6_0_4_7, patch_states6_0_4_8, patch_states6_0_4_9, patch_states6_0_4_10, patch_states6_0_4_11]
theorem final_states6_0_4 : final6_0_4 = stateRows6_0_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
