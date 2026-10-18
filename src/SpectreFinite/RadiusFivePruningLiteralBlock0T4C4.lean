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
def stateRow0_4_4_0 : List State := ParentOwnership.parentRow0283
def patch0_4_4_0 : Patch := literalDomain.zip stateRow0_4_4_0
theorem patch_states0_4_4_0 : patch0_4_4_0.map Prod.snd = stateRow0_4_4_0 := by rfl
def stateRow0_4_4_1 : List State := ParentOwnership.parentRow0586
def patch0_4_4_1 : Patch := literalDomain.zip stateRow0_4_4_1
theorem patch_states0_4_4_1 : patch0_4_4_1.map Prod.snd = stateRow0_4_4_1 := by rfl
def stateRow0_4_4_2 : List State := ParentOwnership.parentRow0588
def patch0_4_4_2 : Patch := literalDomain.zip stateRow0_4_4_2
theorem patch_states0_4_4_2 : patch0_4_4_2.map Prod.snd = stateRow0_4_4_2 := by rfl
def stateRow0_4_4_4 : List State := ParentOwnership.parentRow1302
def patch0_4_4_4 : Patch := literalDomain.zip stateRow0_4_4_4
theorem patch_states0_4_4_4 : patch0_4_4_4.map Prod.snd = stateRow0_4_4_4 := by rfl
def stateRow0_4_4_6 : List State := ParentOwnership.parentRow0133
def patch0_4_4_6 : Patch := literalDomain.zip stateRow0_4_4_6
theorem patch_states0_4_4_6 : patch0_4_4_6.map Prod.snd = stateRow0_4_4_6 := by rfl
def stateRow0_4_4_7 : List State := ParentOwnership.parentRow0277
def patch0_4_4_7 : Patch := literalDomain.zip stateRow0_4_4_7
theorem patch_states0_4_4_7 : patch0_4_4_7.map Prod.snd = stateRow0_4_4_7 := by rfl
def stateRow0_4_4_8 : List State := ParentOwnership.parentRow0824
def patch0_4_4_8 : Patch := literalDomain.zip stateRow0_4_4_8
theorem patch_states0_4_4_8 : patch0_4_4_8.map Prod.snd = stateRow0_4_4_8 := by rfl
def stateRow0_4_4_9 : List State := ParentOwnership.parentRow0825
def patch0_4_4_9 : Patch := literalDomain.zip stateRow0_4_4_9
theorem patch_states0_4_4_9 : patch0_4_4_9.map Prod.snd = stateRow0_4_4_9 := by rfl
def stateRow0_4_4_10 : List State := ParentOwnership.parentRow0584
def patch0_4_4_10 : Patch := literalDomain.zip stateRow0_4_4_10
theorem patch_states0_4_4_10 : patch0_4_4_10.map Prod.snd = stateRow0_4_4_10 := by rfl
def final0_4_4 : List Patch := [patch0_4_4_0, patch0_4_4_1, patch0_4_4_2, patch0_4_4_4, patch0_4_4_6, patch0_4_4_7, patch0_4_4_8, patch0_4_4_9, patch0_4_4_10]
def stateRows0_4_4 : List (List State) := [stateRow0_4_4_0, stateRow0_4_4_1, stateRow0_4_4_2, stateRow0_4_4_4, stateRow0_4_4_6, stateRow0_4_4_7, stateRow0_4_4_8, stateRow0_4_4_9, stateRow0_4_4_10]
theorem stateRows_eq0_4_4 : stateRows0_4_4 = final0_4_4.map (List.map Prod.snd) := by
  simp only [stateRows0_4_4, final0_4_4, List.map_cons, List.map_nil, patch_states0_4_4_0, patch_states0_4_4_1, patch_states0_4_4_2, patch_states0_4_4_4, patch_states0_4_4_6, patch_states0_4_4_7, patch_states0_4_4_8, patch_states0_4_4_9, patch_states0_4_4_10]
theorem final_states0_4_4 : final0_4_4 = stateRows0_4_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
