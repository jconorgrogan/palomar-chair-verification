module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart072
public import SpectreFinite.ParentOwnershipFinitePart073

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow4_5_3_0 : List State := ParentOwnership.parentRow1164
def patch4_5_3_0 : Patch := literalDomain.zip stateRow4_5_3_0
theorem patch_states4_5_3_0 : patch4_5_3_0.map Prod.snd = stateRow4_5_3_0 := by rfl
def stateRow4_5_3_1 : List State := ParentOwnership.parentRow1160
def patch4_5_3_1 : Patch := literalDomain.zip stateRow4_5_3_1
theorem patch_states4_5_3_1 : patch4_5_3_1.map Prod.snd = stateRow4_5_3_1 := by rfl
def stateRow4_5_3_2 : List State := ParentOwnership.parentRow1165
def patch4_5_3_2 : Patch := literalDomain.zip stateRow4_5_3_2
theorem patch_states4_5_3_2 : patch4_5_3_2.map Prod.snd = stateRow4_5_3_2 := by rfl
def stateRow4_5_3_3 : List State := ParentOwnership.parentRow1167
def patch4_5_3_3 : Patch := literalDomain.zip stateRow4_5_3_3
theorem patch_states4_5_3_3 : patch4_5_3_3.map Prod.snd = stateRow4_5_3_3 := by rfl
def stateRow4_5_3_4 : List State := ParentOwnership.parentRow1168
def patch4_5_3_4 : Patch := literalDomain.zip stateRow4_5_3_4
theorem patch_states4_5_3_4 : patch4_5_3_4.map Prod.snd = stateRow4_5_3_4 := by rfl
def stateRow4_5_3_6 : List State := ParentOwnership.parentRow1169
def patch4_5_3_6 : Patch := literalDomain.zip stateRow4_5_3_6
theorem patch_states4_5_3_6 : patch4_5_3_6.map Prod.snd = stateRow4_5_3_6 := by rfl
def stateRow4_5_3_7 : List State := ParentOwnership.parentRow1166
def patch4_5_3_7 : Patch := literalDomain.zip stateRow4_5_3_7
theorem patch_states4_5_3_7 : patch4_5_3_7.map Prod.snd = stateRow4_5_3_7 := by rfl
def stateRow4_5_3_9 : List State := ParentOwnership.parentRow1182
def patch4_5_3_9 : Patch := literalDomain.zip stateRow4_5_3_9
theorem patch_states4_5_3_9 : patch4_5_3_9.map Prod.snd = stateRow4_5_3_9 := by rfl
def final4_5_3 : List Patch := [patch4_5_3_0, patch4_5_3_1, patch4_5_3_2, patch4_5_3_3, patch4_5_3_4, patch4_5_3_6, patch4_5_3_7, patch4_5_3_9]
def stateRows4_5_3 : List (List State) := [stateRow4_5_3_0, stateRow4_5_3_1, stateRow4_5_3_2, stateRow4_5_3_3, stateRow4_5_3_4, stateRow4_5_3_6, stateRow4_5_3_7, stateRow4_5_3_9]
theorem stateRows_eq4_5_3 : stateRows4_5_3 = final4_5_3.map (List.map Prod.snd) := by
  simp only [stateRows4_5_3, final4_5_3, List.map_cons, List.map_nil, patch_states4_5_3_0, patch_states4_5_3_1, patch_states4_5_3_2, patch_states4_5_3_3, patch_states4_5_3_4, patch_states4_5_3_6, patch_states4_5_3_7, patch_states4_5_3_9]
theorem final_states4_5_3 : final4_5_3 = stateRows4_5_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
