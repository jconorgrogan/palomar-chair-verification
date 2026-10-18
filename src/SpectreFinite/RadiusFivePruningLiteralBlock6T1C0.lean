module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart039
public import SpectreFinite.ParentOwnershipFinitePart081
public import SpectreFinite.ParentOwnershipFinitePart082
public import SpectreFinite.ParentOwnershipFinitePart113

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_1_0_2 : List State := ParentOwnership.parentRow1808
def patch6_1_0_2 : Patch := literalDomain.zip stateRow6_1_0_2
theorem patch_states6_1_0_2 : patch6_1_0_2.map Prod.snd = stateRow6_1_0_2 := by rfl
def stateRow6_1_0_3 : List State := ParentOwnership.parentRow0626
def patch6_1_0_3 : Patch := literalDomain.zip stateRow6_1_0_3
theorem patch_states6_1_0_3 : patch6_1_0_3.map Prod.snd = stateRow6_1_0_3 := by rfl
def stateRow6_1_0_5 : List State := ParentOwnership.parentRow0638
def patch6_1_0_5 : Patch := literalDomain.zip stateRow6_1_0_5
theorem patch_states6_1_0_5 : patch6_1_0_5.map Prod.snd = stateRow6_1_0_5 := by rfl
def stateRow6_1_0_6 : List State := ParentOwnership.parentRow0637
def patch6_1_0_6 : Patch := literalDomain.zip stateRow6_1_0_6
theorem patch_states6_1_0_6 : patch6_1_0_6.map Prod.snd = stateRow6_1_0_6 := by rfl
def stateRow6_1_0_8 : List State := ParentOwnership.parentRow1317
def patch6_1_0_8 : Patch := literalDomain.zip stateRow6_1_0_8
theorem patch_states6_1_0_8 : patch6_1_0_8.map Prod.snd = stateRow6_1_0_8 := by rfl
def stateRow6_1_0_10 : List State := ParentOwnership.parentRow1310
def patch6_1_0_10 : Patch := literalDomain.zip stateRow6_1_0_10
theorem patch_states6_1_0_10 : patch6_1_0_10.map Prod.snd = stateRow6_1_0_10 := by rfl
def final6_1_0 : List Patch := [patch6_1_0_2, patch6_1_0_3, patch6_1_0_5, patch6_1_0_6, patch6_1_0_8, patch6_1_0_10]
def stateRows6_1_0 : List (List State) := [stateRow6_1_0_2, stateRow6_1_0_3, stateRow6_1_0_5, stateRow6_1_0_6, stateRow6_1_0_8, stateRow6_1_0_10]
theorem stateRows_eq6_1_0 : stateRows6_1_0 = final6_1_0.map (List.map Prod.snd) := by
  simp only [stateRows6_1_0, final6_1_0, List.map_cons, List.map_nil, patch_states6_1_0_2, patch_states6_1_0_3, patch_states6_1_0_5, patch_states6_1_0_6, patch_states6_1_0_8, patch_states6_1_0_10]
theorem final_states6_1_0 : final6_1_0 = stateRows6_1_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
