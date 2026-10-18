module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart118
public import SpectreFinite.ParentOwnershipFinitePart120
public import SpectreFinite.ParentOwnershipFinitePart121

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_0_0_2 : List State := ParentOwnership.parentRow1920
def patch6_0_0_2 : Patch := literalDomain.zip stateRow6_0_0_2
theorem patch_states6_0_0_2 : patch6_0_0_2.map Prod.snd = stateRow6_0_0_2 := by rfl
def stateRow6_0_0_3 : List State := ParentOwnership.parentRow1937
def patch6_0_0_3 : Patch := literalDomain.zip stateRow6_0_0_3
theorem patch_states6_0_0_3 : patch6_0_0_3.map Prod.snd = stateRow6_0_0_3 := by rfl
def stateRow6_0_0_5 : List State := ParentOwnership.parentRow1939
def patch6_0_0_5 : Patch := literalDomain.zip stateRow6_0_0_5
theorem patch_states6_0_0_5 : patch6_0_0_5.map Prod.snd = stateRow6_0_0_5 := by rfl
def stateRow6_0_0_6 : List State := ParentOwnership.parentRow1940
def patch6_0_0_6 : Patch := literalDomain.zip stateRow6_0_0_6
theorem patch_states6_0_0_6 : patch6_0_0_6.map Prod.snd = stateRow6_0_0_6 := by rfl
def stateRow6_0_0_8 : List State := ParentOwnership.parentRow1891
def patch6_0_0_8 : Patch := literalDomain.zip stateRow6_0_0_8
theorem patch_states6_0_0_8 : patch6_0_0_8.map Prod.snd = stateRow6_0_0_8 := by rfl
def stateRow6_0_0_10 : List State := ParentOwnership.parentRow1898
def patch6_0_0_10 : Patch := literalDomain.zip stateRow6_0_0_10
theorem patch_states6_0_0_10 : patch6_0_0_10.map Prod.snd = stateRow6_0_0_10 := by rfl
def final6_0_0 : List Patch := [patch6_0_0_2, patch6_0_0_3, patch6_0_0_5, patch6_0_0_6, patch6_0_0_8, patch6_0_0_10]
def stateRows6_0_0 : List (List State) := [stateRow6_0_0_2, stateRow6_0_0_3, stateRow6_0_0_5, stateRow6_0_0_6, stateRow6_0_0_8, stateRow6_0_0_10]
theorem stateRows_eq6_0_0 : stateRows6_0_0 = final6_0_0.map (List.map Prod.snd) := by
  simp only [stateRows6_0_0, final6_0_0, List.map_cons, List.map_nil, patch_states6_0_0_2, patch_states6_0_0_3, patch_states6_0_0_5, patch_states6_0_0_6, patch_states6_0_0_8, patch_states6_0_0_10]
theorem final_states6_0_0 : final6_0_0 = stateRows6_0_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
