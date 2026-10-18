module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart034
public import SpectreFinite.ParentOwnershipFinitePart039
public import SpectreFinite.ParentOwnershipFinitePart040

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_0_4_1 : List State := ParentOwnership.parentRow0554
def patch1_0_4_1 : Patch := literalDomain.zip stateRow1_0_4_1
theorem patch_states1_0_4_1 : patch1_0_4_1.map Prod.snd = stateRow1_0_4_1 := by rfl
def stateRow1_0_4_2 : List State := ParentOwnership.parentRow0555
def patch1_0_4_2 : Patch := literalDomain.zip stateRow1_0_4_2
theorem patch_states1_0_4_2 : patch1_0_4_2.map Prod.snd = stateRow1_0_4_2 := by rfl
def stateRow1_0_4_4 : List State := ParentOwnership.parentRow0630
def patch1_0_4_4 : Patch := literalDomain.zip stateRow1_0_4_4
theorem patch_states1_0_4_4 : patch1_0_4_4.map Prod.snd = stateRow1_0_4_4 := by rfl
def stateRow1_0_4_7 : List State := ParentOwnership.parentRow0642
def patch1_0_4_7 : Patch := literalDomain.zip stateRow1_0_4_7
theorem patch_states1_0_4_7 : patch1_0_4_7.map Prod.snd = stateRow1_0_4_7 := by rfl
def stateRow1_0_4_9 : List State := ParentOwnership.parentRow0645
def patch1_0_4_9 : Patch := literalDomain.zip stateRow1_0_4_9
theorem patch_states1_0_4_9 : patch1_0_4_9.map Prod.snd = stateRow1_0_4_9 := by rfl
def stateRow1_0_4_10 : List State := ParentOwnership.parentRow0646
def patch1_0_4_10 : Patch := literalDomain.zip stateRow1_0_4_10
theorem patch_states1_0_4_10 : patch1_0_4_10.map Prod.snd = stateRow1_0_4_10 := by rfl
def final1_0_4 : List Patch := [patch1_0_4_1, patch1_0_4_2, patch1_0_4_4, patch1_0_4_7, patch1_0_4_9, patch1_0_4_10]
def stateRows1_0_4 : List (List State) := [stateRow1_0_4_1, stateRow1_0_4_2, stateRow1_0_4_4, stateRow1_0_4_7, stateRow1_0_4_9, stateRow1_0_4_10]
theorem stateRows_eq1_0_4 : stateRows1_0_4 = final1_0_4.map (List.map Prod.snd) := by
  simp only [stateRows1_0_4, final1_0_4, List.map_cons, List.map_nil, patch_states1_0_4_1, patch_states1_0_4_2, patch_states1_0_4_4, patch_states1_0_4_7, patch_states1_0_4_9, patch_states1_0_4_10]
theorem final_states1_0_4 : final1_0_4 = stateRows1_0_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
