module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart061
public import SpectreFinite.ParentOwnershipFinitePart062
public import SpectreFinite.ParentOwnershipFinitePart127
public import SpectreFinite.ParentOwnershipFinitePart128

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow4_0_1_0 : List State := ParentOwnership.parentRow0989
def patch4_0_1_0 : Patch := literalDomain.zip stateRow4_0_1_0
theorem patch_states4_0_1_0 : patch4_0_1_0.map Prod.snd = stateRow4_0_1_0 := by rfl
def stateRow4_0_1_1 : List State := ParentOwnership.parentRow0990
def patch4_0_1_1 : Patch := literalDomain.zip stateRow4_0_1_1
theorem patch_states4_0_1_1 : patch4_0_1_1.map Prod.snd = stateRow4_0_1_1 := by rfl
def stateRow4_0_1_3 : List State := ParentOwnership.parentRow0991
def patch4_0_1_3 : Patch := literalDomain.zip stateRow4_0_1_3
theorem patch_states4_0_1_3 : patch4_0_1_3.map Prod.snd = stateRow4_0_1_3 := by rfl
def stateRow4_0_1_4 : List State := ParentOwnership.parentRow0992
def patch4_0_1_4 : Patch := literalDomain.zip stateRow4_0_1_4
theorem patch_states4_0_1_4 : patch4_0_1_4.map Prod.snd = stateRow4_0_1_4 := by rfl
def stateRow4_0_1_5 : List State := ParentOwnership.parentRow2041
def patch4_0_1_5 : Patch := literalDomain.zip stateRow4_0_1_5
theorem patch_states4_0_1_5 : patch4_0_1_5.map Prod.snd = stateRow4_0_1_5 := by rfl
def stateRow4_0_1_6 : List State := ParentOwnership.parentRow2047
def patch4_0_1_6 : Patch := literalDomain.zip stateRow4_0_1_6
theorem patch_states4_0_1_6 : patch4_0_1_6.map Prod.snd = stateRow4_0_1_6 := by rfl
def stateRow4_0_1_7 : List State := ParentOwnership.parentRow2052
def patch4_0_1_7 : Patch := literalDomain.zip stateRow4_0_1_7
theorem patch_states4_0_1_7 : patch4_0_1_7.map Prod.snd = stateRow4_0_1_7 := by rfl
def stateRow4_0_1_8 : List State := ParentOwnership.parentRow2053
def patch4_0_1_8 : Patch := literalDomain.zip stateRow4_0_1_8
theorem patch_states4_0_1_8 : patch4_0_1_8.map Prod.snd = stateRow4_0_1_8 := by rfl
def stateRow4_0_1_10 : List State := ParentOwnership.parentRow2054
def patch4_0_1_10 : Patch := literalDomain.zip stateRow4_0_1_10
theorem patch_states4_0_1_10 : patch4_0_1_10.map Prod.snd = stateRow4_0_1_10 := by rfl
def final4_0_1 : List Patch := [patch4_0_1_0, patch4_0_1_1, patch4_0_1_3, patch4_0_1_4, patch4_0_1_5, patch4_0_1_6, patch4_0_1_7, patch4_0_1_8, patch4_0_1_10]
def stateRows4_0_1 : List (List State) := [stateRow4_0_1_0, stateRow4_0_1_1, stateRow4_0_1_3, stateRow4_0_1_4, stateRow4_0_1_5, stateRow4_0_1_6, stateRow4_0_1_7, stateRow4_0_1_8, stateRow4_0_1_10]
theorem stateRows_eq4_0_1 : stateRows4_0_1 = final4_0_1.map (List.map Prod.snd) := by
  simp only [stateRows4_0_1, final4_0_1, List.map_cons, List.map_nil, patch_states4_0_1_0, patch_states4_0_1_1, patch_states4_0_1_3, patch_states4_0_1_4, patch_states4_0_1_5, patch_states4_0_1_6, patch_states4_0_1_7, patch_states4_0_1_8, patch_states4_0_1_10]
theorem final_states4_0_1 : final4_0_1 = stateRows4_0_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
