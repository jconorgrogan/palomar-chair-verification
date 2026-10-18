module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart008
public import SpectreFinite.ParentOwnershipFinitePart017
public import SpectreFinite.ParentOwnershipFinitePart036
public import SpectreFinite.ParentOwnershipFinitePart051
public import SpectreFinite.ParentOwnershipFinitePart081

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_4_3_0 : List State := ParentOwnership.parentRow0137
def patch0_4_3_0 : Patch := literalDomain.zip stateRow0_4_3_0
theorem patch_states0_4_3_0 : patch0_4_3_0.map Prod.snd = stateRow0_4_3_0 := by rfl
def stateRow0_4_3_2 : List State := ParentOwnership.parentRow0282
def patch0_4_3_2 : Patch := literalDomain.zip stateRow0_4_3_2
theorem patch_states0_4_3_2 : patch0_4_3_2.map Prod.snd = stateRow0_4_3_2 := by rfl
def stateRow0_4_3_3 : List State := ParentOwnership.parentRow0828
def patch0_4_3_3 : Patch := literalDomain.zip stateRow0_4_3_3
theorem patch_states0_4_3_3 : patch0_4_3_3.map Prod.snd = stateRow0_4_3_3 := by rfl
def stateRow0_4_3_4 : List State := ParentOwnership.parentRow0829
def patch0_4_3_4 : Patch := literalDomain.zip stateRow0_4_3_4
theorem patch_states0_4_3_4 : patch0_4_3_4.map Prod.snd = stateRow0_4_3_4 := by rfl
def stateRow0_4_3_5 : List State := ParentOwnership.parentRow0587
def patch0_4_3_5 : Patch := literalDomain.zip stateRow0_4_3_5
theorem patch_states0_4_3_5 : patch0_4_3_5.map Prod.snd = stateRow0_4_3_5 := by rfl
def stateRow0_4_3_6 : List State := ParentOwnership.parentRow1299
def patch0_4_3_6 : Patch := literalDomain.zip stateRow0_4_3_6
theorem patch_states0_4_3_6 : patch0_4_3_6.map Prod.snd = stateRow0_4_3_6 := by rfl
def stateRow0_4_3_8 : List State := ParentOwnership.parentRow0138
def patch0_4_3_8 : Patch := literalDomain.zip stateRow0_4_3_8
theorem patch_states0_4_3_8 : patch0_4_3_8.map Prod.snd = stateRow0_4_3_8 := by rfl
def stateRow0_4_3_9 : List State := ParentOwnership.parentRow1301
def patch0_4_3_9 : Patch := literalDomain.zip stateRow0_4_3_9
theorem patch_states0_4_3_9 : patch0_4_3_9.map Prod.snd = stateRow0_4_3_9 := by rfl
def stateRow0_4_3_11 : List State := ParentOwnership.parentRow0281
def patch0_4_3_11 : Patch := literalDomain.zip stateRow0_4_3_11
theorem patch_states0_4_3_11 : patch0_4_3_11.map Prod.snd = stateRow0_4_3_11 := by rfl
def final0_4_3 : List Patch := [patch0_4_3_0, patch0_4_3_2, patch0_4_3_3, patch0_4_3_4, patch0_4_3_5, patch0_4_3_6, patch0_4_3_8, patch0_4_3_9, patch0_4_3_11]
def stateRows0_4_3 : List (List State) := [stateRow0_4_3_0, stateRow0_4_3_2, stateRow0_4_3_3, stateRow0_4_3_4, stateRow0_4_3_5, stateRow0_4_3_6, stateRow0_4_3_8, stateRow0_4_3_9, stateRow0_4_3_11]
theorem stateRows_eq0_4_3 : stateRows0_4_3 = final0_4_3.map (List.map Prod.snd) := by
  simp only [stateRows0_4_3, final0_4_3, List.map_cons, List.map_nil, patch_states0_4_3_0, patch_states0_4_3_2, patch_states0_4_3_3, patch_states0_4_3_4, patch_states0_4_3_5, patch_states0_4_3_6, patch_states0_4_3_8, patch_states0_4_3_9, patch_states0_4_3_11]
theorem final_states0_4_3 : final0_4_3 = stateRows0_4_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
