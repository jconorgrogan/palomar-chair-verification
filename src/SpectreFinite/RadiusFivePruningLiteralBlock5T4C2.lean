module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart034
public import SpectreFinite.ParentOwnershipFinitePart035
public import SpectreFinite.ParentOwnershipFinitePart036
public import SpectreFinite.ParentOwnershipFinitePart041
public import SpectreFinite.ParentOwnershipFinitePart049

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_4_2_0 : List State := ParentOwnership.parentRow0799
def patch5_4_2_0 : Patch := literalDomain.zip stateRow5_4_2_0
theorem patch_states5_4_2_0 : patch5_4_2_0.map Prod.snd = stateRow5_4_2_0 := by rfl
def stateRow5_4_2_1 : List State := ParentOwnership.parentRow0580
def patch5_4_2_1 : Patch := literalDomain.zip stateRow5_4_2_1
theorem patch_states5_4_2_1 : patch5_4_2_1.map Prod.snd = stateRow5_4_2_1 := by rfl
def stateRow5_4_2_2 : List State := ParentOwnership.parentRow0666
def patch5_4_2_2 : Patch := literalDomain.zip stateRow5_4_2_2
theorem patch_states5_4_2_2 : patch5_4_2_2.map Prod.snd = stateRow5_4_2_2 := by rfl
def stateRow5_4_2_3 : List State := ParentOwnership.parentRow0668
def patch5_4_2_3 : Patch := literalDomain.zip stateRow5_4_2_3
theorem patch_states5_4_2_3 : patch5_4_2_3.map Prod.snd = stateRow5_4_2_3 := by rfl
def stateRow5_4_2_4 : List State := ParentOwnership.parentRow0571
def patch5_4_2_4 : Patch := literalDomain.zip stateRow5_4_2_4
theorem patch_states5_4_2_4 : patch5_4_2_4.map Prod.snd = stateRow5_4_2_4 := by rfl
def stateRow5_4_2_5 : List State := ParentOwnership.parentRow0559
def patch5_4_2_5 : Patch := literalDomain.zip stateRow5_4_2_5
theorem patch_states5_4_2_5 : patch5_4_2_5.map Prod.snd = stateRow5_4_2_5 := by rfl
def stateRow5_4_2_6 : List State := ParentOwnership.parentRow0667
def patch5_4_2_6 : Patch := literalDomain.zip stateRow5_4_2_6
theorem patch_states5_4_2_6 : patch5_4_2_6.map Prod.snd = stateRow5_4_2_6 := by rfl
def stateRow5_4_2_7 : List State := ParentOwnership.parentRow0669
def patch5_4_2_7 : Patch := literalDomain.zip stateRow5_4_2_7
theorem patch_states5_4_2_7 : patch5_4_2_7.map Prod.snd = stateRow5_4_2_7 := by rfl
def stateRow5_4_2_8 : List State := ParentOwnership.parentRow0572
def patch5_4_2_8 : Patch := literalDomain.zip stateRow5_4_2_8
theorem patch_states5_4_2_8 : patch5_4_2_8.map Prod.snd = stateRow5_4_2_8 := by rfl
def stateRow5_4_2_9 : List State := ParentOwnership.parentRow0560
def patch5_4_2_9 : Patch := literalDomain.zip stateRow5_4_2_9
theorem patch_states5_4_2_9 : patch5_4_2_9.map Prod.snd = stateRow5_4_2_9 := by rfl
def stateRow5_4_2_10 : List State := ParentOwnership.parentRow0664
def patch5_4_2_10 : Patch := literalDomain.zip stateRow5_4_2_10
theorem patch_states5_4_2_10 : patch5_4_2_10.map Prod.snd = stateRow5_4_2_10 := by rfl
def final5_4_2 : List Patch := [patch5_4_2_0, patch5_4_2_1, patch5_4_2_2, patch5_4_2_3, patch5_4_2_4, patch5_4_2_5, patch5_4_2_6, patch5_4_2_7, patch5_4_2_8, patch5_4_2_9, patch5_4_2_10]
def stateRows5_4_2 : List (List State) := [stateRow5_4_2_0, stateRow5_4_2_1, stateRow5_4_2_2, stateRow5_4_2_3, stateRow5_4_2_4, stateRow5_4_2_5, stateRow5_4_2_6, stateRow5_4_2_7, stateRow5_4_2_8, stateRow5_4_2_9, stateRow5_4_2_10]
theorem stateRows_eq5_4_2 : stateRows5_4_2 = final5_4_2.map (List.map Prod.snd) := by
  simp only [stateRows5_4_2, final5_4_2, List.map_cons, List.map_nil, patch_states5_4_2_0, patch_states5_4_2_1, patch_states5_4_2_2, patch_states5_4_2_3, patch_states5_4_2_4, patch_states5_4_2_5, patch_states5_4_2_6, patch_states5_4_2_7, patch_states5_4_2_8, patch_states5_4_2_9, patch_states5_4_2_10]
theorem final_states5_4_2 : final5_4_2 = stateRows5_4_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
