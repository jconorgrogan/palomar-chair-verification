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
def stateRow0_2_4_0 : List State := ParentOwnership.parentRow1917
def patch0_2_4_0 : Patch := literalDomain.zip stateRow0_2_4_0
theorem patch_states0_2_4_0 : patch0_2_4_0.map Prod.snd = stateRow0_2_4_0 := by rfl
def stateRow0_2_4_1 : List State := ParentOwnership.parentRow1905
def patch0_2_4_1 : Patch := literalDomain.zip stateRow0_2_4_1
theorem patch_states0_2_4_1 : patch0_2_4_1.map Prod.snd = stateRow0_2_4_1 := by rfl
def stateRow0_2_4_2 : List State := ParentOwnership.parentRow1918
def patch0_2_4_2 : Patch := literalDomain.zip stateRow0_2_4_2
theorem patch_states0_2_4_2 : patch0_2_4_2.map Prod.snd = stateRow0_2_4_2 := by rfl
def stateRow0_2_4_4 : List State := ParentOwnership.parentRow1001
def patch0_2_4_4 : Patch := literalDomain.zip stateRow0_2_4_4
theorem patch_states0_2_4_4 : patch0_2_4_4.map Prod.snd = stateRow0_2_4_4 := by rfl
def stateRow0_2_4_6 : List State := ParentOwnership.parentRow1936
def patch0_2_4_6 : Patch := literalDomain.zip stateRow0_2_4_6
theorem patch_states0_2_4_6 : patch0_2_4_6.map Prod.snd = stateRow0_2_4_6 := by rfl
def stateRow0_2_4_7 : List State := ParentOwnership.parentRow1932
def patch0_2_4_7 : Patch := literalDomain.zip stateRow0_2_4_7
theorem patch_states0_2_4_7 : patch0_2_4_7.map Prod.snd = stateRow0_2_4_7 := by rfl
def stateRow0_2_4_8 : List State := ParentOwnership.parentRow0888
def patch0_2_4_8 : Patch := literalDomain.zip stateRow0_2_4_8
theorem patch_states0_2_4_8 : patch0_2_4_8.map Prod.snd = stateRow0_2_4_8 := by rfl
def stateRow0_2_4_9 : List State := ParentOwnership.parentRow1945
def patch0_2_4_9 : Patch := literalDomain.zip stateRow0_2_4_9
theorem patch_states0_2_4_9 : patch0_2_4_9.map Prod.snd = stateRow0_2_4_9 := by rfl
def stateRow0_2_4_10 : List State := ParentOwnership.parentRow1933
def patch0_2_4_10 : Patch := literalDomain.zip stateRow0_2_4_10
theorem patch_states0_2_4_10 : patch0_2_4_10.map Prod.snd = stateRow0_2_4_10 := by rfl
def final0_2_4 : List Patch := [patch0_2_4_0, patch0_2_4_1, patch0_2_4_2, patch0_2_4_4, patch0_2_4_6, patch0_2_4_7, patch0_2_4_8, patch0_2_4_9, patch0_2_4_10]
def stateRows0_2_4 : List (List State) := [stateRow0_2_4_0, stateRow0_2_4_1, stateRow0_2_4_2, stateRow0_2_4_4, stateRow0_2_4_6, stateRow0_2_4_7, stateRow0_2_4_8, stateRow0_2_4_9, stateRow0_2_4_10]
theorem stateRows_eq0_2_4 : stateRows0_2_4 = final0_2_4.map (List.map Prod.snd) := by
  simp only [stateRows0_2_4, final0_2_4, List.map_cons, List.map_nil, patch_states0_2_4_0, patch_states0_2_4_1, patch_states0_2_4_2, patch_states0_2_4_4, patch_states0_2_4_6, patch_states0_2_4_7, patch_states0_2_4_8, patch_states0_2_4_9, patch_states0_2_4_10]
theorem final_states0_2_4 : final0_2_4 = stateRows0_2_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
