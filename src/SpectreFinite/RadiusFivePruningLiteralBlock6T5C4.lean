module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart043
public import SpectreFinite.ParentOwnershipFinitePart054
public import SpectreFinite.ParentOwnershipFinitePart055
public import SpectreFinite.ParentOwnershipFinitePart062
public import SpectreFinite.ParentOwnershipFinitePart083
public import SpectreFinite.ParentOwnershipFinitePart085
public import SpectreFinite.ParentOwnershipFinitePart118

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_5_4_0 : List State := ParentOwnership.parentRow0694
def patch6_5_4_0 : Patch := literalDomain.zip stateRow6_5_4_0
theorem patch_states6_5_4_0 : patch6_5_4_0.map Prod.snd = stateRow6_5_4_0 := by rfl
def stateRow6_5_4_1 : List State := ParentOwnership.parentRow1365
def patch6_5_4_1 : Patch := literalDomain.zip stateRow6_5_4_1
theorem patch_states6_5_4_1 : patch6_5_4_1.map Prod.snd = stateRow6_5_4_1 := by rfl
def stateRow6_5_4_2 : List State := ParentOwnership.parentRow1341
def patch6_5_4_2 : Patch := literalDomain.zip stateRow6_5_4_2
theorem patch_states6_5_4_2 : patch6_5_4_2.map Prod.snd = stateRow6_5_4_2 := by rfl
def stateRow6_5_4_3 : List State := ParentOwnership.parentRow0878
def patch6_5_4_3 : Patch := literalDomain.zip stateRow6_5_4_3
theorem patch_states6_5_4_3 : patch6_5_4_3.map Prod.snd = stateRow6_5_4_3 := by rfl
def stateRow6_5_4_4 : List State := ParentOwnership.parentRow0879
def patch6_5_4_4 : Patch := literalDomain.zip stateRow6_5_4_4
theorem patch_states6_5_4_4 : patch6_5_4_4.map Prod.snd = stateRow6_5_4_4 := by rfl
def stateRow6_5_4_5 : List State := ParentOwnership.parentRow1892
def patch6_5_4_5 : Patch := literalDomain.zip stateRow6_5_4_5
theorem patch_states6_5_4_5 : patch6_5_4_5.map Prod.snd = stateRow6_5_4_5 := by rfl
def stateRow6_5_4_6 : List State := ParentOwnership.parentRow1893
def patch6_5_4_6 : Patch := literalDomain.zip stateRow6_5_4_6
theorem patch_states6_5_4_6 : patch6_5_4_6.map Prod.snd = stateRow6_5_4_6 := by rfl
def stateRow6_5_4_7 : List State := ParentOwnership.parentRow1000
def patch6_5_4_7 : Patch := literalDomain.zip stateRow6_5_4_7
theorem patch_states6_5_4_7 : patch6_5_4_7.map Prod.snd = stateRow6_5_4_7 := by rfl
def stateRow6_5_4_8 : List State := ParentOwnership.parentRow0881
def patch6_5_4_8 : Patch := literalDomain.zip stateRow6_5_4_8
theorem patch_states6_5_4_8 : patch6_5_4_8.map Prod.snd = stateRow6_5_4_8 := by rfl
def stateRow6_5_4_9 : List State := ParentOwnership.parentRow0882
def patch6_5_4_9 : Patch := literalDomain.zip stateRow6_5_4_9
theorem patch_states6_5_4_9 : patch6_5_4_9.map Prod.snd = stateRow6_5_4_9 := by rfl
def stateRow6_5_4_10 : List State := ParentOwnership.parentRow1895
def patch6_5_4_10 : Patch := literalDomain.zip stateRow6_5_4_10
theorem patch_states6_5_4_10 : patch6_5_4_10.map Prod.snd = stateRow6_5_4_10 := by rfl
def stateRow6_5_4_11 : List State := ParentOwnership.parentRow1896
def patch6_5_4_11 : Patch := literalDomain.zip stateRow6_5_4_11
theorem patch_states6_5_4_11 : patch6_5_4_11.map Prod.snd = stateRow6_5_4_11 := by rfl
def final6_5_4 : List Patch := [patch6_5_4_0, patch6_5_4_1, patch6_5_4_2, patch6_5_4_3, patch6_5_4_4, patch6_5_4_5, patch6_5_4_6, patch6_5_4_7, patch6_5_4_8, patch6_5_4_9, patch6_5_4_10, patch6_5_4_11]
def stateRows6_5_4 : List (List State) := [stateRow6_5_4_0, stateRow6_5_4_1, stateRow6_5_4_2, stateRow6_5_4_3, stateRow6_5_4_4, stateRow6_5_4_5, stateRow6_5_4_6, stateRow6_5_4_7, stateRow6_5_4_8, stateRow6_5_4_9, stateRow6_5_4_10, stateRow6_5_4_11]
theorem stateRows_eq6_5_4 : stateRows6_5_4 = final6_5_4.map (List.map Prod.snd) := by
  simp only [stateRows6_5_4, final6_5_4, List.map_cons, List.map_nil, patch_states6_5_4_0, patch_states6_5_4_1, patch_states6_5_4_2, patch_states6_5_4_3, patch_states6_5_4_4, patch_states6_5_4_5, patch_states6_5_4_6, patch_states6_5_4_7, patch_states6_5_4_8, patch_states6_5_4_9, patch_states6_5_4_10, patch_states6_5_4_11]
theorem final_states6_5_4 : final6_5_4 = stateRows6_5_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
