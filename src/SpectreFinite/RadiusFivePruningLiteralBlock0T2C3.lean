module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart055
public import SpectreFinite.ParentOwnershipFinitePart062
public import SpectreFinite.ParentOwnershipFinitePart119
public import SpectreFinite.ParentOwnershipFinitePart120
public import SpectreFinite.ParentOwnershipFinitePart121

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_2_3_0 : List State := ParentOwnership.parentRow1916
def patch0_2_3_0 : Patch := literalDomain.zip stateRow0_2_3_0
theorem patch_states0_2_3_0 : patch0_2_3_0.map Prod.snd = stateRow0_2_3_0 := by rfl
def stateRow0_2_3_2 : List State := ParentOwnership.parentRow1934
def patch0_2_3_2 : Patch := literalDomain.zip stateRow0_2_3_2
theorem patch_states0_2_3_2 : patch0_2_3_2.map Prod.snd = stateRow0_2_3_2 := by rfl
def stateRow0_2_3_3 : List State := ParentOwnership.parentRow0889
def patch0_2_3_3 : Patch := literalDomain.zip stateRow0_2_3_3
theorem patch_states0_2_3_3 : patch0_2_3_3.map Prod.snd = stateRow0_2_3_3 := by rfl
def stateRow0_2_3_4 : List State := ParentOwnership.parentRow1946
def patch0_2_3_4 : Patch := literalDomain.zip stateRow0_2_3_4
theorem patch_states0_2_3_4 : patch0_2_3_4.map Prod.snd = stateRow0_2_3_4 := by rfl
def stateRow0_2_3_5 : List State := ParentOwnership.parentRow1935
def patch0_2_3_5 : Patch := literalDomain.zip stateRow0_2_3_5
theorem patch_states0_2_3_5 : patch0_2_3_5.map Prod.snd = stateRow0_2_3_5 := by rfl
def stateRow0_2_3_6 : List State := ParentOwnership.parentRow1006
def patch0_2_3_6 : Patch := literalDomain.zip stateRow0_2_3_6
theorem patch_states0_2_3_6 : patch0_2_3_6.map Prod.snd = stateRow0_2_3_6 := by rfl
def stateRow0_2_3_8 : List State := ParentOwnership.parentRow1919
def patch0_2_3_8 : Patch := literalDomain.zip stateRow0_2_3_8
theorem patch_states0_2_3_8 : patch0_2_3_8.map Prod.snd = stateRow0_2_3_8 := by rfl
def stateRow0_2_3_9 : List State := ParentOwnership.parentRow0884
def patch0_2_3_9 : Patch := literalDomain.zip stateRow0_2_3_9
theorem patch_states0_2_3_9 : patch0_2_3_9.map Prod.snd = stateRow0_2_3_9 := by rfl
def stateRow0_2_3_11 : List State := ParentOwnership.parentRow1904
def patch0_2_3_11 : Patch := literalDomain.zip stateRow0_2_3_11
theorem patch_states0_2_3_11 : patch0_2_3_11.map Prod.snd = stateRow0_2_3_11 := by rfl
def final0_2_3 : List Patch := [patch0_2_3_0, patch0_2_3_2, patch0_2_3_3, patch0_2_3_4, patch0_2_3_5, patch0_2_3_6, patch0_2_3_8, patch0_2_3_9, patch0_2_3_11]
def stateRows0_2_3 : List (List State) := [stateRow0_2_3_0, stateRow0_2_3_2, stateRow0_2_3_3, stateRow0_2_3_4, stateRow0_2_3_5, stateRow0_2_3_6, stateRow0_2_3_8, stateRow0_2_3_9, stateRow0_2_3_11]
theorem stateRows_eq0_2_3 : stateRows0_2_3 = final0_2_3.map (List.map Prod.snd) := by
  simp only [stateRows0_2_3, final0_2_3, List.map_cons, List.map_nil, patch_states0_2_3_0, patch_states0_2_3_2, patch_states0_2_3_3, patch_states0_2_3_4, patch_states0_2_3_5, patch_states0_2_3_6, patch_states0_2_3_8, patch_states0_2_3_9, patch_states0_2_3_11]
theorem final_states0_2_3 : final0_2_3 = stateRows0_2_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
