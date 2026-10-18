module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart038
public import SpectreFinite.ParentOwnershipFinitePart128

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_5_0_2 : List State := ParentOwnership.parentRow2060
def patch6_5_0_2 : Patch := literalDomain.zip stateRow6_5_0_2
theorem patch_states6_5_0_2 : patch6_5_0_2.map Prod.snd = stateRow6_5_0_2 := by rfl
def stateRow6_5_0_3 : List State := ParentOwnership.parentRow2062
def patch6_5_0_3 : Patch := literalDomain.zip stateRow6_5_0_3
theorem patch_states6_5_0_3 : patch6_5_0_3.map Prod.snd = stateRow6_5_0_3 := by rfl
def stateRow6_5_0_5 : List State := ParentOwnership.parentRow2063
def patch6_5_0_5 : Patch := literalDomain.zip stateRow6_5_0_5
theorem patch_states6_5_0_5 : patch6_5_0_5.map Prod.snd = stateRow6_5_0_5 := by rfl
def stateRow6_5_0_6 : List State := ParentOwnership.parentRow2061
def patch6_5_0_6 : Patch := literalDomain.zip stateRow6_5_0_6
theorem patch_states6_5_0_6 : patch6_5_0_6.map Prod.snd = stateRow6_5_0_6 := by rfl
def stateRow6_5_0_8 : List State := ParentOwnership.parentRow0614
def patch6_5_0_8 : Patch := literalDomain.zip stateRow6_5_0_8
theorem patch_states6_5_0_8 : patch6_5_0_8.map Prod.snd = stateRow6_5_0_8 := by rfl
def stateRow6_5_0_10 : List State := ParentOwnership.parentRow0615
def patch6_5_0_10 : Patch := literalDomain.zip stateRow6_5_0_10
theorem patch_states6_5_0_10 : patch6_5_0_10.map Prod.snd = stateRow6_5_0_10 := by rfl
def final6_5_0 : List Patch := [patch6_5_0_2, patch6_5_0_3, patch6_5_0_5, patch6_5_0_6, patch6_5_0_8, patch6_5_0_10]
def stateRows6_5_0 : List (List State) := [stateRow6_5_0_2, stateRow6_5_0_3, stateRow6_5_0_5, stateRow6_5_0_6, stateRow6_5_0_8, stateRow6_5_0_10]
theorem stateRows_eq6_5_0 : stateRows6_5_0 = final6_5_0.map (List.map Prod.snd) := by
  simp only [stateRows6_5_0, final6_5_0, List.map_cons, List.map_nil, patch_states6_5_0_2, patch_states6_5_0_3, patch_states6_5_0_5, patch_states6_5_0_6, patch_states6_5_0_8, patch_states6_5_0_10]
theorem final_states6_5_0 : final6_5_0 = stateRows6_5_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
