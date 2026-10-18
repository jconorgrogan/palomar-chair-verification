module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart017
public import SpectreFinite.ParentOwnershipFinitePart018
public import SpectreFinite.ParentOwnershipFinitePart019
public import SpectreFinite.ParentOwnershipFinitePart066
public import SpectreFinite.ParentOwnershipFinitePart068

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_2_3_0 : List State := ParentOwnership.parentRow1089
def patch6_2_3_0 : Patch := literalDomain.zip stateRow6_2_3_0
theorem patch_states6_2_3_0 : patch6_2_3_0.map Prod.snd = stateRow6_2_3_0 := by rfl
def stateRow6_2_3_1 : List State := ParentOwnership.parentRow0299
def patch6_2_3_1 : Patch := literalDomain.zip stateRow6_2_3_1
theorem patch_states6_2_3_1 : patch6_2_3_1.map Prod.snd = stateRow6_2_3_1 := by rfl
def stateRow6_2_3_4 : List State := ParentOwnership.parentRow0305
def patch6_2_3_4 : Patch := literalDomain.zip stateRow6_2_3_4
theorem patch_states6_2_3_4 : patch6_2_3_4.map Prod.snd = stateRow6_2_3_4 := by rfl
def stateRow6_2_3_5 : List State := ParentOwnership.parentRow1060
def patch6_2_3_5 : Patch := literalDomain.zip stateRow6_2_3_5
theorem patch_states6_2_3_5 : patch6_2_3_5.map Prod.snd = stateRow6_2_3_5 := by rfl
def stateRow6_2_3_6 : List State := ParentOwnership.parentRow0297
def patch6_2_3_6 : Patch := literalDomain.zip stateRow6_2_3_6
theorem patch_states6_2_3_6 : patch6_2_3_6.map Prod.snd = stateRow6_2_3_6 := by rfl
def stateRow6_2_3_7 : List State := ParentOwnership.parentRow0306
def patch6_2_3_7 : Patch := literalDomain.zip stateRow6_2_3_7
theorem patch_states6_2_3_7 : patch6_2_3_7.map Prod.snd = stateRow6_2_3_7 := by rfl
def stateRow6_2_3_8 : List State := ParentOwnership.parentRow0298
def patch6_2_3_8 : Patch := literalDomain.zip stateRow6_2_3_8
theorem patch_states6_2_3_8 : patch6_2_3_8.map Prod.snd = stateRow6_2_3_8 := by rfl
def stateRow6_2_3_9 : List State := ParentOwnership.parentRow0307
def patch6_2_3_9 : Patch := literalDomain.zip stateRow6_2_3_9
theorem patch_states6_2_3_9 : patch6_2_3_9.map Prod.snd = stateRow6_2_3_9 := by rfl
def stateRow6_2_3_10 : List State := ParentOwnership.parentRow0284
def patch6_2_3_10 : Patch := literalDomain.zip stateRow6_2_3_10
theorem patch_states6_2_3_10 : patch6_2_3_10.map Prod.snd = stateRow6_2_3_10 := by rfl
def stateRow6_2_3_11 : List State := ParentOwnership.parentRow0286
def patch6_2_3_11 : Patch := literalDomain.zip stateRow6_2_3_11
theorem patch_states6_2_3_11 : patch6_2_3_11.map Prod.snd = stateRow6_2_3_11 := by rfl
def final6_2_3 : List Patch := [patch6_2_3_0, patch6_2_3_1, patch6_2_3_4, patch6_2_3_5, patch6_2_3_6, patch6_2_3_7, patch6_2_3_8, patch6_2_3_9, patch6_2_3_10, patch6_2_3_11]
def stateRows6_2_3 : List (List State) := [stateRow6_2_3_0, stateRow6_2_3_1, stateRow6_2_3_4, stateRow6_2_3_5, stateRow6_2_3_6, stateRow6_2_3_7, stateRow6_2_3_8, stateRow6_2_3_9, stateRow6_2_3_10, stateRow6_2_3_11]
theorem stateRows_eq6_2_3 : stateRows6_2_3 = final6_2_3.map (List.map Prod.snd) := by
  simp only [stateRows6_2_3, final6_2_3, List.map_cons, List.map_nil, patch_states6_2_3_0, patch_states6_2_3_1, patch_states6_2_3_4, patch_states6_2_3_5, patch_states6_2_3_6, patch_states6_2_3_7, patch_states6_2_3_8, patch_states6_2_3_9, patch_states6_2_3_10, patch_states6_2_3_11]
theorem final_states6_2_3 : final6_2_3 = stateRows6_2_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
