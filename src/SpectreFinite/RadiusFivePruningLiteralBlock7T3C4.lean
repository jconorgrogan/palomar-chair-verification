module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart002
public import SpectreFinite.ParentOwnershipFinitePart016
public import SpectreFinite.ParentOwnershipFinitePart071
public import SpectreFinite.ParentOwnershipFinitePart073
public import SpectreFinite.ParentOwnershipFinitePart074

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_3_4_1 : List State := ParentOwnership.parentRow1171
def patch7_3_4_1 : Patch := literalDomain.zip stateRow7_3_4_1
theorem patch_states7_3_4_1 : patch7_3_4_1.map Prod.snd = stateRow7_3_4_1 := by rfl
def stateRow7_3_4_2 : List State := ParentOwnership.parentRow0268
def patch7_3_4_2 : Patch := literalDomain.zip stateRow7_3_4_2
theorem patch_states7_3_4_2 : patch7_3_4_2.map Prod.snd = stateRow7_3_4_2 := by rfl
def stateRow7_3_4_3 : List State := ParentOwnership.parentRow1194
def patch7_3_4_3 : Patch := literalDomain.zip stateRow7_3_4_3
theorem patch_states7_3_4_3 : patch7_3_4_3.map Prod.snd = stateRow7_3_4_3 := by rfl
def stateRow7_3_4_4 : List State := ParentOwnership.parentRow1197
def patch7_3_4_4 : Patch := literalDomain.zip stateRow7_3_4_4
theorem patch_states7_3_4_4 : patch7_3_4_4.map Prod.snd = stateRow7_3_4_4 := by rfl
def stateRow7_3_4_5 : List State := ParentOwnership.parentRow0265
def patch7_3_4_5 : Patch := literalDomain.zip stateRow7_3_4_5
theorem patch_states7_3_4_5 : patch7_3_4_5.map Prod.snd = stateRow7_3_4_5 := by rfl
def stateRow7_3_4_8 : List State := ParentOwnership.parentRow0036
def patch7_3_4_8 : Patch := literalDomain.zip stateRow7_3_4_8
theorem patch_states7_3_4_8 : patch7_3_4_8.map Prod.snd = stateRow7_3_4_8 := by rfl
def stateRow7_3_4_10 : List State := ParentOwnership.parentRow1141
def patch7_3_4_10 : Patch := literalDomain.zip stateRow7_3_4_10
theorem patch_states7_3_4_10 : patch7_3_4_10.map Prod.snd = stateRow7_3_4_10 := by rfl
def final7_3_4 : List Patch := [patch7_3_4_1, patch7_3_4_2, patch7_3_4_3, patch7_3_4_4, patch7_3_4_5, patch7_3_4_8, patch7_3_4_10]
def stateRows7_3_4 : List (List State) := [stateRow7_3_4_1, stateRow7_3_4_2, stateRow7_3_4_3, stateRow7_3_4_4, stateRow7_3_4_5, stateRow7_3_4_8, stateRow7_3_4_10]
theorem stateRows_eq7_3_4 : stateRows7_3_4 = final7_3_4.map (List.map Prod.snd) := by
  simp only [stateRows7_3_4, final7_3_4, List.map_cons, List.map_nil, patch_states7_3_4_1, patch_states7_3_4_2, patch_states7_3_4_3, patch_states7_3_4_4, patch_states7_3_4_5, patch_states7_3_4_8, patch_states7_3_4_10]
theorem final_states7_3_4 : final7_3_4 = stateRows7_3_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
