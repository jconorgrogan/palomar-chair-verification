module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart009
public import SpectreFinite.ParentOwnershipFinitePart011
public import SpectreFinite.ParentOwnershipFinitePart065
public import SpectreFinite.ParentOwnershipFinitePart069

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_5_4_0 : List State := ParentOwnership.parentRow0177
def patch0_5_4_0 : Patch := literalDomain.zip stateRow0_5_4_0
theorem patch_states0_5_4_0 : patch0_5_4_0.map Prod.snd = stateRow0_5_4_0 := by rfl
def stateRow0_5_4_1 : List State := ParentOwnership.parentRow1117
def patch0_5_4_1 : Patch := literalDomain.zip stateRow0_5_4_1
theorem patch_states0_5_4_1 : patch0_5_4_1.map Prod.snd = stateRow0_5_4_1 := by rfl
def stateRow0_5_4_2 : List State := ParentOwnership.parentRow1118
def patch0_5_4_2 : Patch := literalDomain.zip stateRow0_5_4_2
theorem patch_states0_5_4_2 : patch0_5_4_2.map Prod.snd = stateRow0_5_4_2 := by rfl
def stateRow0_5_4_4 : List State := ParentOwnership.parentRow0179
def patch0_5_4_4 : Patch := literalDomain.zip stateRow0_5_4_4
theorem patch_states0_5_4_4 : patch0_5_4_4.map Prod.snd = stateRow0_5_4_4 := by rfl
def stateRow0_5_4_6 : List State := ParentOwnership.parentRow1040
def patch0_5_4_6 : Patch := literalDomain.zip stateRow0_5_4_6
theorem patch_states0_5_4_6 : patch0_5_4_6.map Prod.snd = stateRow0_5_4_6 := by rfl
def stateRow0_5_4_7 : List State := ParentOwnership.parentRow0146
def patch0_5_4_7 : Patch := literalDomain.zip stateRow0_5_4_7
theorem patch_states0_5_4_7 : patch0_5_4_7.map Prod.snd = stateRow0_5_4_7 := by rfl
def stateRow0_5_4_8 : List State := ParentOwnership.parentRow1105
def patch0_5_4_8 : Patch := literalDomain.zip stateRow0_5_4_8
theorem patch_states0_5_4_8 : patch0_5_4_8.map Prod.snd = stateRow0_5_4_8 := by rfl
def stateRow0_5_4_9 : List State := ParentOwnership.parentRow1106
def patch0_5_4_9 : Patch := literalDomain.zip stateRow0_5_4_9
theorem patch_states0_5_4_9 : patch0_5_4_9.map Prod.snd = stateRow0_5_4_9 := by rfl
def stateRow0_5_4_10 : List State := ParentOwnership.parentRow1107
def patch0_5_4_10 : Patch := literalDomain.zip stateRow0_5_4_10
theorem patch_states0_5_4_10 : patch0_5_4_10.map Prod.snd = stateRow0_5_4_10 := by rfl
def final0_5_4 : List Patch := [patch0_5_4_0, patch0_5_4_1, patch0_5_4_2, patch0_5_4_4, patch0_5_4_6, patch0_5_4_7, patch0_5_4_8, patch0_5_4_9, patch0_5_4_10]
def stateRows0_5_4 : List (List State) := [stateRow0_5_4_0, stateRow0_5_4_1, stateRow0_5_4_2, stateRow0_5_4_4, stateRow0_5_4_6, stateRow0_5_4_7, stateRow0_5_4_8, stateRow0_5_4_9, stateRow0_5_4_10]
theorem stateRows_eq0_5_4 : stateRows0_5_4 = final0_5_4.map (List.map Prod.snd) := by
  simp only [stateRows0_5_4, final0_5_4, List.map_cons, List.map_nil, patch_states0_5_4_0, patch_states0_5_4_1, patch_states0_5_4_2, patch_states0_5_4_4, patch_states0_5_4_6, patch_states0_5_4_7, patch_states0_5_4_8, patch_states0_5_4_9, patch_states0_5_4_10]
theorem final_states0_5_4 : final0_5_4 = stateRows0_5_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
