module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart062

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_5_5_0 : List State := ParentOwnership.parentRow1002
def patch6_5_5_0 : Patch := literalDomain.zip stateRow6_5_5_0
theorem patch_states6_5_5_0 : patch6_5_5_0.map Prod.snd = stateRow6_5_5_0 := by rfl
def stateRow6_5_5_1 : List State := ParentOwnership.parentRow1003
def patch6_5_5_1 : Patch := literalDomain.zip stateRow6_5_5_1
theorem patch_states6_5_5_1 : patch6_5_5_1.map Prod.snd = stateRow6_5_5_1 := by rfl
def stateRow6_5_5_2 : List State := ParentOwnership.parentRow1004
def patch6_5_5_2 : Patch := literalDomain.zip stateRow6_5_5_2
theorem patch_states6_5_5_2 : patch6_5_5_2.map Prod.snd = stateRow6_5_5_2 := by rfl
def final6_5_5 : List Patch := [patch6_5_5_0, patch6_5_5_1, patch6_5_5_2]
def stateRows6_5_5 : List (List State) := [stateRow6_5_5_0, stateRow6_5_5_1, stateRow6_5_5_2]
theorem stateRows_eq6_5_5 : stateRows6_5_5 = final6_5_5.map (List.map Prod.snd) := by
  simp only [stateRows6_5_5, final6_5_5, List.map_cons, List.map_nil, patch_states6_5_5_0, patch_states6_5_5_1, patch_states6_5_5_2]
theorem final_states6_5_5 : final6_5_5 = stateRows6_5_5.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
