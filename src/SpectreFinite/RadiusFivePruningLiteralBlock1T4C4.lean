module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart106
public import SpectreFinite.ParentOwnershipFinitePart108
public import SpectreFinite.ParentOwnershipFinitePart109
public import SpectreFinite.ParentOwnershipFinitePart129

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_4_4_1 : List State := ParentOwnership.parentRow1698
def patch1_4_4_1 : Patch := literalDomain.zip stateRow1_4_4_1
theorem patch_states1_4_4_1 : patch1_4_4_1.map Prod.snd = stateRow1_4_4_1 := by rfl
def stateRow1_4_4_2 : List State := ParentOwnership.parentRow1733
def patch1_4_4_2 : Patch := literalDomain.zip stateRow1_4_4_2
theorem patch_states1_4_4_2 : patch1_4_4_2.map Prod.snd = stateRow1_4_4_2 := by rfl
def stateRow1_4_4_4 : List State := ParentOwnership.parentRow1753
def patch1_4_4_4 : Patch := literalDomain.zip stateRow1_4_4_4
theorem patch_states1_4_4_4 : patch1_4_4_4.map Prod.snd = stateRow1_4_4_4 := by rfl
def stateRow1_4_4_7 : List State := ParentOwnership.parentRow2073
def patch1_4_4_7 : Patch := literalDomain.zip stateRow1_4_4_7
theorem patch_states1_4_4_7 : patch1_4_4_7.map Prod.snd = stateRow1_4_4_7 := by rfl
def stateRow1_4_4_9 : List State := ParentOwnership.parentRow2072
def patch1_4_4_9 : Patch := literalDomain.zip stateRow1_4_4_9
theorem patch_states1_4_4_9 : patch1_4_4_9.map Prod.snd = stateRow1_4_4_9 := by rfl
def stateRow1_4_4_10 : List State := ParentOwnership.parentRow1758
def patch1_4_4_10 : Patch := literalDomain.zip stateRow1_4_4_10
theorem patch_states1_4_4_10 : patch1_4_4_10.map Prod.snd = stateRow1_4_4_10 := by rfl
def final1_4_4 : List Patch := [patch1_4_4_1, patch1_4_4_2, patch1_4_4_4, patch1_4_4_7, patch1_4_4_9, patch1_4_4_10]
def stateRows1_4_4 : List (List State) := [stateRow1_4_4_1, stateRow1_4_4_2, stateRow1_4_4_4, stateRow1_4_4_7, stateRow1_4_4_9, stateRow1_4_4_10]
theorem stateRows_eq1_4_4 : stateRows1_4_4 = final1_4_4.map (List.map Prod.snd) := by
  simp only [stateRows1_4_4, final1_4_4, List.map_cons, List.map_nil, patch_states1_4_4_1, patch_states1_4_4_2, patch_states1_4_4_4, patch_states1_4_4_7, patch_states1_4_4_9, patch_states1_4_4_10]
theorem final_states1_4_4 : final1_4_4 = stateRows1_4_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
