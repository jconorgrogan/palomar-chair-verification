module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart086
public import SpectreFinite.ParentOwnershipFinitePart087
public import SpectreFinite.ParentOwnershipFinitePart089
public import SpectreFinite.ParentOwnershipFinitePart090
public import SpectreFinite.ParentOwnershipFinitePart114

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow4_4_2_0 : List State := ParentOwnership.parentRow1438
def patch4_4_2_0 : Patch := literalDomain.zip stateRow4_4_2_0
theorem patch_states4_4_2_0 : patch4_4_2_0.map Prod.snd = stateRow4_4_2_0 := by rfl
def stateRow4_4_2_1 : List State := ParentOwnership.parentRow1444
def patch4_4_2_1 : Patch := literalDomain.zip stateRow4_4_2_1
theorem patch_states4_4_2_1 : patch4_4_2_1.map Prod.snd = stateRow4_4_2_1 := by rfl
def stateRow4_4_2_2 : List State := ParentOwnership.parentRow1437
def patch4_4_2_2 : Patch := literalDomain.zip stateRow4_4_2_2
theorem patch_states4_4_2_2 : patch4_4_2_2.map Prod.snd = stateRow4_4_2_2 := by rfl
def stateRow4_4_2_4 : List State := ParentOwnership.parentRow1443
def patch4_4_2_4 : Patch := literalDomain.zip stateRow4_4_2_4
theorem patch_states4_4_2_4 : patch4_4_2_4.map Prod.snd = stateRow4_4_2_4 := by rfl
def stateRow4_4_2_6 : List State := ParentOwnership.parentRow1828
def patch4_4_2_6 : Patch := literalDomain.zip stateRow4_4_2_6
theorem patch_states4_4_2_6 : patch4_4_2_6.map Prod.snd = stateRow4_4_2_6 := by rfl
def stateRow4_4_2_7 : List State := ParentOwnership.parentRow1829
def patch4_4_2_7 : Patch := literalDomain.zip stateRow4_4_2_7
theorem patch_states4_4_2_7 : patch4_4_2_7.map Prod.snd = stateRow4_4_2_7 := by rfl
def stateRow4_4_2_9 : List State := ParentOwnership.parentRow1398
def patch4_4_2_9 : Patch := literalDomain.zip stateRow4_4_2_9
theorem patch_states4_4_2_9 : patch4_4_2_9.map Prod.snd = stateRow4_4_2_9 := by rfl
def stateRow4_4_2_10 : List State := ParentOwnership.parentRow1830
def patch4_4_2_10 : Patch := literalDomain.zip stateRow4_4_2_10
theorem patch_states4_4_2_10 : patch4_4_2_10.map Prod.snd = stateRow4_4_2_10 := by rfl
def stateRow4_4_2_11 : List State := ParentOwnership.parentRow1385
def patch4_4_2_11 : Patch := literalDomain.zip stateRow4_4_2_11
theorem patch_states4_4_2_11 : patch4_4_2_11.map Prod.snd = stateRow4_4_2_11 := by rfl
def final4_4_2 : List Patch := [patch4_4_2_0, patch4_4_2_1, patch4_4_2_2, patch4_4_2_4, patch4_4_2_6, patch4_4_2_7, patch4_4_2_9, patch4_4_2_10, patch4_4_2_11]
def stateRows4_4_2 : List (List State) := [stateRow4_4_2_0, stateRow4_4_2_1, stateRow4_4_2_2, stateRow4_4_2_4, stateRow4_4_2_6, stateRow4_4_2_7, stateRow4_4_2_9, stateRow4_4_2_10, stateRow4_4_2_11]
theorem stateRows_eq4_4_2 : stateRows4_4_2 = final4_4_2.map (List.map Prod.snd) := by
  simp only [stateRows4_4_2, final4_4_2, List.map_cons, List.map_nil, patch_states4_4_2_0, patch_states4_4_2_1, patch_states4_4_2_2, patch_states4_4_2_4, patch_states4_4_2_6, patch_states4_4_2_7, patch_states4_4_2_9, patch_states4_4_2_10, patch_states4_4_2_11]
theorem final_states4_4_2 : final4_4_2 = stateRows4_4_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
