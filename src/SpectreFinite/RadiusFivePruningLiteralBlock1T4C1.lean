module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart032
public import SpectreFinite.ParentOwnershipFinitePart033
public import SpectreFinite.ParentOwnershipFinitePart034
public import SpectreFinite.ParentOwnershipFinitePart105

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_4_1_1 : List State := ParentOwnership.parentRow0543
def patch1_4_1_1 : Patch := literalDomain.zip stateRow1_4_1_1
theorem patch_states1_4_1_1 : patch1_4_1_1.map Prod.snd = stateRow1_4_1_1 := by rfl
def stateRow1_4_1_2 : List State := ParentOwnership.parentRow0545
def patch1_4_1_2 : Patch := literalDomain.zip stateRow1_4_1_2
theorem patch_states1_4_1_2 : patch1_4_1_2.map Prod.snd = stateRow1_4_1_2 := by rfl
def stateRow1_4_1_3 : List State := ParentOwnership.parentRow0544
def patch1_4_1_3 : Patch := literalDomain.zip stateRow1_4_1_3
theorem patch_states1_4_1_3 : patch1_4_1_3.map Prod.snd = stateRow1_4_1_3 := by rfl
def stateRow1_4_1_4 : List State := ParentOwnership.parentRow0546
def patch1_4_1_4 : Patch := literalDomain.zip stateRow1_4_1_4
theorem patch_states1_4_1_4 : patch1_4_1_4.map Prod.snd = stateRow1_4_1_4 := by rfl
def stateRow1_4_1_5 : List State := ParentOwnership.parentRow1683
def patch1_4_1_5 : Patch := literalDomain.zip stateRow1_4_1_5
theorem patch_states1_4_1_5 : patch1_4_1_5.map Prod.snd = stateRow1_4_1_5 := by rfl
def stateRow1_4_1_6 : List State := ParentOwnership.parentRow0526
def patch1_4_1_6 : Patch := literalDomain.zip stateRow1_4_1_6
theorem patch_states1_4_1_6 : patch1_4_1_6.map Prod.snd = stateRow1_4_1_6 := by rfl
def stateRow1_4_1_8 : List State := ParentOwnership.parentRow0527
def patch1_4_1_8 : Patch := literalDomain.zip stateRow1_4_1_8
theorem patch_states1_4_1_8 : patch1_4_1_8.map Prod.snd = stateRow1_4_1_8 := by rfl
def stateRow1_4_1_9 : List State := ParentOwnership.parentRow0528
def patch1_4_1_9 : Patch := literalDomain.zip stateRow1_4_1_9
theorem patch_states1_4_1_9 : patch1_4_1_9.map Prod.snd = stateRow1_4_1_9 := by rfl
def stateRow1_4_1_10 : List State := ParentOwnership.parentRow0517
def patch1_4_1_10 : Patch := literalDomain.zip stateRow1_4_1_10
theorem patch_states1_4_1_10 : patch1_4_1_10.map Prod.snd = stateRow1_4_1_10 := by rfl
def final1_4_1 : List Patch := [patch1_4_1_1, patch1_4_1_2, patch1_4_1_3, patch1_4_1_4, patch1_4_1_5, patch1_4_1_6, patch1_4_1_8, patch1_4_1_9, patch1_4_1_10]
def stateRows1_4_1 : List (List State) := [stateRow1_4_1_1, stateRow1_4_1_2, stateRow1_4_1_3, stateRow1_4_1_4, stateRow1_4_1_5, stateRow1_4_1_6, stateRow1_4_1_8, stateRow1_4_1_9, stateRow1_4_1_10]
theorem stateRows_eq1_4_1 : stateRows1_4_1 = final1_4_1.map (List.map Prod.snd) := by
  simp only [stateRows1_4_1, final1_4_1, List.map_cons, List.map_nil, patch_states1_4_1_1, patch_states1_4_1_2, patch_states1_4_1_3, patch_states1_4_1_4, patch_states1_4_1_5, patch_states1_4_1_6, patch_states1_4_1_8, patch_states1_4_1_9, patch_states1_4_1_10]
theorem final_states1_4_1 : final1_4_1 = stateRows1_4_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
