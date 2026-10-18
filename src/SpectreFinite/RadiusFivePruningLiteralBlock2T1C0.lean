module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart097
public import SpectreFinite.ParentOwnershipFinitePart099
public import SpectreFinite.ParentOwnershipFinitePart100

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow2_1_0_1 : List State := ParentOwnership.parentRow1561
def patch2_1_0_1 : Patch := literalDomain.zip stateRow2_1_0_1
theorem patch_states2_1_0_1 : patch2_1_0_1.map Prod.snd = stateRow2_1_0_1 := by rfl
def stateRow2_1_0_2 : List State := ParentOwnership.parentRow1599
def patch2_1_0_2 : Patch := literalDomain.zip stateRow2_1_0_2
theorem patch_states2_1_0_2 : patch2_1_0_2.map Prod.snd = stateRow2_1_0_2 := by rfl
def stateRow2_1_0_3 : List State := ParentOwnership.parentRow1602
def patch2_1_0_3 : Patch := literalDomain.zip stateRow2_1_0_3
theorem patch_states2_1_0_3 : patch2_1_0_3.map Prod.snd = stateRow2_1_0_3 := by rfl
def stateRow2_1_0_5 : List State := ParentOwnership.parentRow1558
def patch2_1_0_5 : Patch := literalDomain.zip stateRow2_1_0_5
theorem patch_states2_1_0_5 : patch2_1_0_5.map Prod.snd = stateRow2_1_0_5 := by rfl
def final2_1_0 : List Patch := [patch2_1_0_1, patch2_1_0_2, patch2_1_0_3, patch2_1_0_5]
def stateRows2_1_0 : List (List State) := [stateRow2_1_0_1, stateRow2_1_0_2, stateRow2_1_0_3, stateRow2_1_0_5]
theorem stateRows_eq2_1_0 : stateRows2_1_0 = final2_1_0.map (List.map Prod.snd) := by
  simp only [stateRows2_1_0, final2_1_0, List.map_cons, List.map_nil, patch_states2_1_0_1, patch_states2_1_0_2, patch_states2_1_0_3, patch_states2_1_0_5]
theorem final_states2_1_0 : final2_1_0 = stateRows2_1_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
