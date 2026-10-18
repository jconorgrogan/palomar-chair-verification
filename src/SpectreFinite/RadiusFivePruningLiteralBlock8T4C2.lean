module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart087
public import SpectreFinite.ParentOwnershipFinitePart088
public import SpectreFinite.ParentOwnershipFinitePart089
public import SpectreFinite.ParentOwnershipFinitePart116
public import SpectreFinite.ParentOwnershipFinitePart117

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_4_2_0 : List State := ParentOwnership.parentRow1871
def patch8_4_2_0 : Patch := literalDomain.zip stateRow8_4_2_0
theorem patch_states8_4_2_0 : patch8_4_2_0.map Prod.snd = stateRow8_4_2_0 := by rfl
def stateRow8_4_2_2 : List State := ParentOwnership.parentRow1884
def patch8_4_2_2 : Patch := literalDomain.zip stateRow8_4_2_2
theorem patch_states8_4_2_2 : patch8_4_2_2.map Prod.snd = stateRow8_4_2_2 := by rfl
def stateRow8_4_2_3 : List State := ParentOwnership.parentRow1885
def patch8_4_2_3 : Patch := literalDomain.zip stateRow8_4_2_3
theorem patch_states8_4_2_3 : patch8_4_2_3.map Prod.snd = stateRow8_4_2_3 := by rfl
def stateRow8_4_2_4 : List State := ParentOwnership.parentRow1868
def patch8_4_2_4 : Patch := literalDomain.zip stateRow8_4_2_4
theorem patch_states8_4_2_4 : patch8_4_2_4.map Prod.snd = stateRow8_4_2_4 := by rfl
def stateRow8_4_2_5 : List State := ParentOwnership.parentRow1869
def patch8_4_2_5 : Patch := literalDomain.zip stateRow8_4_2_5
theorem patch_states8_4_2_5 : patch8_4_2_5.map Prod.snd = stateRow8_4_2_5 := by rfl
def stateRow8_4_2_6 : List State := ParentOwnership.parentRow1419
def patch8_4_2_6 : Patch := literalDomain.zip stateRow8_4_2_6
theorem patch_states8_4_2_6 : patch8_4_2_6.map Prod.snd = stateRow8_4_2_6 := by rfl
def stateRow8_4_2_7 : List State := ParentOwnership.parentRow1418
def patch8_4_2_7 : Patch := literalDomain.zip stateRow8_4_2_7
theorem patch_states8_4_2_7 : patch8_4_2_7.map Prod.snd = stateRow8_4_2_7 := by rfl
def stateRow8_4_2_8 : List State := ParentOwnership.parentRow1426
def patch8_4_2_8 : Patch := literalDomain.zip stateRow8_4_2_8
theorem patch_states8_4_2_8 : patch8_4_2_8.map Prod.snd = stateRow8_4_2_8 := by rfl
def stateRow8_4_2_9 : List State := ParentOwnership.parentRow1396
def patch8_4_2_9 : Patch := literalDomain.zip stateRow8_4_2_9
theorem patch_states8_4_2_9 : patch8_4_2_9.map Prod.snd = stateRow8_4_2_9 := by rfl
def stateRow8_4_2_10 : List State := ParentOwnership.parentRow1425
def patch8_4_2_10 : Patch := literalDomain.zip stateRow8_4_2_10
theorem patch_states8_4_2_10 : patch8_4_2_10.map Prod.snd = stateRow8_4_2_10 := by rfl
def stateRow8_4_2_11 : List State := ParentOwnership.parentRow1395
def patch8_4_2_11 : Patch := literalDomain.zip stateRow8_4_2_11
theorem patch_states8_4_2_11 : patch8_4_2_11.map Prod.snd = stateRow8_4_2_11 := by rfl
def final8_4_2 : List Patch := [patch8_4_2_0, patch8_4_2_2, patch8_4_2_3, patch8_4_2_4, patch8_4_2_5, patch8_4_2_6, patch8_4_2_7, patch8_4_2_8, patch8_4_2_9, patch8_4_2_10, patch8_4_2_11]
def stateRows8_4_2 : List (List State) := [stateRow8_4_2_0, stateRow8_4_2_2, stateRow8_4_2_3, stateRow8_4_2_4, stateRow8_4_2_5, stateRow8_4_2_6, stateRow8_4_2_7, stateRow8_4_2_8, stateRow8_4_2_9, stateRow8_4_2_10, stateRow8_4_2_11]
theorem stateRows_eq8_4_2 : stateRows8_4_2 = final8_4_2.map (List.map Prod.snd) := by
  simp only [stateRows8_4_2, final8_4_2, List.map_cons, List.map_nil, patch_states8_4_2_0, patch_states8_4_2_2, patch_states8_4_2_3, patch_states8_4_2_4, patch_states8_4_2_5, patch_states8_4_2_6, patch_states8_4_2_7, patch_states8_4_2_8, patch_states8_4_2_9, patch_states8_4_2_10, patch_states8_4_2_11]
theorem final_states8_4_2 : final8_4_2 = stateRows8_4_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
