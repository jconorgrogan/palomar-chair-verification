module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart097
public import SpectreFinite.ParentOwnershipFinitePart099
public import SpectreFinite.ParentOwnershipFinitePart100
public import SpectreFinite.ParentOwnershipFinitePart122

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow4_1_1_0 : List State := ParentOwnership.parentRow1594
def patch4_1_1_0 : Patch := literalDomain.zip stateRow4_1_1_0
theorem patch_states4_1_1_0 : patch4_1_1_0.map Prod.snd = stateRow4_1_1_0 := by rfl
def stateRow4_1_1_1 : List State := ParentOwnership.parentRow1595
def patch4_1_1_1 : Patch := literalDomain.zip stateRow4_1_1_1
theorem patch_states4_1_1_1 : patch4_1_1_1.map Prod.snd = stateRow4_1_1_1 := by rfl
def stateRow4_1_1_3 : List State := ParentOwnership.parentRow1598
def patch4_1_1_3 : Patch := literalDomain.zip stateRow4_1_1_3
theorem patch_states4_1_1_3 : patch4_1_1_3.map Prod.snd = stateRow4_1_1_3 := by rfl
def stateRow4_1_1_4 : List State := ParentOwnership.parentRow1600
def patch4_1_1_4 : Patch := literalDomain.zip stateRow4_1_1_4
theorem patch_states4_1_1_4 : patch4_1_1_4.map Prod.snd = stateRow4_1_1_4 := by rfl
def stateRow4_1_1_5 : List State := ParentOwnership.parentRow1962
def patch4_1_1_5 : Patch := literalDomain.zip stateRow4_1_1_5
theorem patch_states4_1_1_5 : patch4_1_1_5.map Prod.snd = stateRow4_1_1_5 := by rfl
def stateRow4_1_1_6 : List State := ParentOwnership.parentRow1560
def patch4_1_1_6 : Patch := literalDomain.zip stateRow4_1_1_6
theorem patch_states4_1_1_6 : patch4_1_1_6.map Prod.snd = stateRow4_1_1_6 := by rfl
def stateRow4_1_1_7 : List State := ParentOwnership.parentRow1596
def patch4_1_1_7 : Patch := literalDomain.zip stateRow4_1_1_7
theorem patch_states4_1_1_7 : patch4_1_1_7.map Prod.snd = stateRow4_1_1_7 := by rfl
def stateRow4_1_1_8 : List State := ParentOwnership.parentRow1597
def patch4_1_1_8 : Patch := literalDomain.zip stateRow4_1_1_8
theorem patch_states4_1_1_8 : patch4_1_1_8.map Prod.snd = stateRow4_1_1_8 := by rfl
def stateRow4_1_1_10 : List State := ParentOwnership.parentRow1601
def patch4_1_1_10 : Patch := literalDomain.zip stateRow4_1_1_10
theorem patch_states4_1_1_10 : patch4_1_1_10.map Prod.snd = stateRow4_1_1_10 := by rfl
def final4_1_1 : List Patch := [patch4_1_1_0, patch4_1_1_1, patch4_1_1_3, patch4_1_1_4, patch4_1_1_5, patch4_1_1_6, patch4_1_1_7, patch4_1_1_8, patch4_1_1_10]
def stateRows4_1_1 : List (List State) := [stateRow4_1_1_0, stateRow4_1_1_1, stateRow4_1_1_3, stateRow4_1_1_4, stateRow4_1_1_5, stateRow4_1_1_6, stateRow4_1_1_7, stateRow4_1_1_8, stateRow4_1_1_10]
theorem stateRows_eq4_1_1 : stateRows4_1_1 = final4_1_1.map (List.map Prod.snd) := by
  simp only [stateRows4_1_1, final4_1_1, List.map_cons, List.map_nil, patch_states4_1_1_0, patch_states4_1_1_1, patch_states4_1_1_3, patch_states4_1_1_4, patch_states4_1_1_5, patch_states4_1_1_6, patch_states4_1_1_7, patch_states4_1_1_8, patch_states4_1_1_10]
theorem final_states4_1_1 : final4_1_1 = stateRows4_1_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
