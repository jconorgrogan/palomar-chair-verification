module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart027
public import SpectreFinite.ParentOwnershipFinitePart028

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow2_5_0_1 : List State := ParentOwnership.parentRow0454
def patch2_5_0_1 : Patch := literalDomain.zip stateRow2_5_0_1
theorem patch_states2_5_0_1 : patch2_5_0_1.map Prod.snd = stateRow2_5_0_1 := by rfl
def stateRow2_5_0_2 : List State := ParentOwnership.parentRow0453
def patch2_5_0_2 : Patch := literalDomain.zip stateRow2_5_0_2
theorem patch_states2_5_0_2 : patch2_5_0_2.map Prod.snd = stateRow2_5_0_2 := by rfl
def stateRow2_5_0_3 : List State := ParentOwnership.parentRow0455
def patch2_5_0_3 : Patch := literalDomain.zip stateRow2_5_0_3
theorem patch_states2_5_0_3 : patch2_5_0_3.map Prod.snd = stateRow2_5_0_3 := by rfl
def stateRow2_5_0_5 : List State := ParentOwnership.parentRow0440
def patch2_5_0_5 : Patch := literalDomain.zip stateRow2_5_0_5
theorem patch_states2_5_0_5 : patch2_5_0_5.map Prod.snd = stateRow2_5_0_5 := by rfl
def final2_5_0 : List Patch := [patch2_5_0_1, patch2_5_0_2, patch2_5_0_3, patch2_5_0_5]
def stateRows2_5_0 : List (List State) := [stateRow2_5_0_1, stateRow2_5_0_2, stateRow2_5_0_3, stateRow2_5_0_5]
theorem stateRows_eq2_5_0 : stateRows2_5_0 = final2_5_0.map (List.map Prod.snd) := by
  simp only [stateRows2_5_0, final2_5_0, List.map_cons, List.map_nil, patch_states2_5_0_1, patch_states2_5_0_2, patch_states2_5_0_3, patch_states2_5_0_5]
theorem final_states2_5_0 : final2_5_0 = stateRows2_5_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
