module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart086
public import SpectreFinite.ParentOwnershipFinitePart087
public import SpectreFinite.ParentOwnershipFinitePart089
public import SpectreFinite.ParentOwnershipFinitePart114

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow4_4_3_0 : List State := ParentOwnership.parentRow1831
def patch4_4_3_0 : Patch := literalDomain.zip stateRow4_4_3_0
theorem patch_states4_4_3_0 : patch4_4_3_0.map Prod.snd = stateRow4_4_3_0 := by rfl
def stateRow4_4_3_1 : List State := ParentOwnership.parentRow1386
def patch4_4_3_1 : Patch := literalDomain.zip stateRow4_4_3_1
theorem patch_states4_4_3_1 : patch4_4_3_1.map Prod.snd = stateRow4_4_3_1 := by rfl
def stateRow4_4_3_2 : List State := ParentOwnership.parentRow1406
def patch4_4_3_2 : Patch := literalDomain.zip stateRow4_4_3_2
theorem patch_states4_4_3_2 : patch4_4_3_2.map Prod.snd = stateRow4_4_3_2 := by rfl
def stateRow4_4_3_3 : List State := ParentOwnership.parentRow1832
def patch4_4_3_3 : Patch := literalDomain.zip stateRow4_4_3_3
theorem patch_states4_4_3_3 : patch4_4_3_3.map Prod.snd = stateRow4_4_3_3 := by rfl
def stateRow4_4_3_4 : List State := ParentOwnership.parentRow1833
def patch4_4_3_4 : Patch := literalDomain.zip stateRow4_4_3_4
theorem patch_states4_4_3_4 : patch4_4_3_4.map Prod.snd = stateRow4_4_3_4 := by rfl
def stateRow4_4_3_6 : List State := ParentOwnership.parentRow1834
def patch4_4_3_6 : Patch := literalDomain.zip stateRow4_4_3_6
theorem patch_states4_4_3_6 : patch4_4_3_6.map Prod.snd = stateRow4_4_3_6 := by rfl
def stateRow4_4_3_7 : List State := ParentOwnership.parentRow1390
def patch4_4_3_7 : Patch := literalDomain.zip stateRow4_4_3_7
theorem patch_states4_4_3_7 : patch4_4_3_7.map Prod.snd = stateRow4_4_3_7 := by rfl
def stateRow4_4_3_9 : List State := ParentOwnership.parentRow1428
def patch4_4_3_9 : Patch := literalDomain.zip stateRow4_4_3_9
theorem patch_states4_4_3_9 : patch4_4_3_9.map Prod.snd = stateRow4_4_3_9 := by rfl
def final4_4_3 : List Patch := [patch4_4_3_0, patch4_4_3_1, patch4_4_3_2, patch4_4_3_3, patch4_4_3_4, patch4_4_3_6, patch4_4_3_7, patch4_4_3_9]
def stateRows4_4_3 : List (List State) := [stateRow4_4_3_0, stateRow4_4_3_1, stateRow4_4_3_2, stateRow4_4_3_3, stateRow4_4_3_4, stateRow4_4_3_6, stateRow4_4_3_7, stateRow4_4_3_9]
theorem stateRows_eq4_4_3 : stateRows4_4_3 = final4_4_3.map (List.map Prod.snd) := by
  simp only [stateRows4_4_3, final4_4_3, List.map_cons, List.map_nil, patch_states4_4_3_0, patch_states4_4_3_1, patch_states4_4_3_2, patch_states4_4_3_3, patch_states4_4_3_4, patch_states4_4_3_6, patch_states4_4_3_7, patch_states4_4_3_9]
theorem final_states4_4_3 : final4_4_3 = stateRows4_4_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
