module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart054
public import SpectreFinite.ParentOwnershipFinitePart087
public import SpectreFinite.ParentOwnershipFinitePart117
public import SpectreFinite.ParentOwnershipFinitePart118

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow4_4_0_1 : List State := ParentOwnership.parentRow1876
def patch4_4_0_1 : Patch := literalDomain.zip stateRow4_4_0_1
theorem patch_states4_4_0_1 : patch4_4_0_1.map Prod.snd = stateRow4_4_0_1 := by rfl
def stateRow4_4_0_3 : List State := ParentOwnership.parentRow1875
def patch4_4_0_3 : Patch := literalDomain.zip stateRow4_4_0_3
theorem patch_states4_4_0_3 : patch4_4_0_3.map Prod.snd = stateRow4_4_0_3 := by rfl
def stateRow4_4_0_4 : List State := ParentOwnership.parentRow0876
def patch4_4_0_4 : Patch := literalDomain.zip stateRow4_4_0_4
theorem patch_states4_4_0_4 : patch4_4_0_4.map Prod.snd = stateRow4_4_0_4 := by rfl
def stateRow4_4_0_6 : List State := ParentOwnership.parentRow1877
def patch4_4_0_6 : Patch := literalDomain.zip stateRow4_4_0_6
theorem patch_states4_4_0_6 : patch4_4_0_6.map Prod.snd = stateRow4_4_0_6 := by rfl
def stateRow4_4_0_7 : List State := ParentOwnership.parentRow1889
def patch4_4_0_7 : Patch := literalDomain.zip stateRow4_4_0_7
theorem patch_states4_4_0_7 : patch4_4_0_7.map Prod.snd = stateRow4_4_0_7 := by rfl
def stateRow4_4_0_9 : List State := ParentOwnership.parentRow1878
def patch4_4_0_9 : Patch := literalDomain.zip stateRow4_4_0_9
theorem patch_states4_4_0_9 : patch4_4_0_9.map Prod.snd = stateRow4_4_0_9 := by rfl
def stateRow4_4_0_10 : List State := ParentOwnership.parentRow1890
def patch4_4_0_10 : Patch := literalDomain.zip stateRow4_4_0_10
theorem patch_states4_4_0_10 : patch4_4_0_10.map Prod.snd = stateRow4_4_0_10 := by rfl
def stateRow4_4_0_11 : List State := ParentOwnership.parentRow1405
def patch4_4_0_11 : Patch := literalDomain.zip stateRow4_4_0_11
theorem patch_states4_4_0_11 : patch4_4_0_11.map Prod.snd = stateRow4_4_0_11 := by rfl
def final4_4_0 : List Patch := [patch4_4_0_1, patch4_4_0_3, patch4_4_0_4, patch4_4_0_6, patch4_4_0_7, patch4_4_0_9, patch4_4_0_10, patch4_4_0_11]
def stateRows4_4_0 : List (List State) := [stateRow4_4_0_1, stateRow4_4_0_3, stateRow4_4_0_4, stateRow4_4_0_6, stateRow4_4_0_7, stateRow4_4_0_9, stateRow4_4_0_10, stateRow4_4_0_11]
theorem stateRows_eq4_4_0 : stateRows4_4_0 = final4_4_0.map (List.map Prod.snd) := by
  simp only [stateRows4_4_0, final4_4_0, List.map_cons, List.map_nil, patch_states4_4_0_1, patch_states4_4_0_3, patch_states4_4_0_4, patch_states4_4_0_6, patch_states4_4_0_7, patch_states4_4_0_9, patch_states4_4_0_10, patch_states4_4_0_11]
theorem final_states4_4_0 : final4_4_0 = stateRows4_4_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
