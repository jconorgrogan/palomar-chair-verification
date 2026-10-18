module

public import SpectreFinite.RadiusFivePruningBlock6T3C1Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation6_3_1_0 : rotatedStateRow3 sourceState6_1_0 = stateRow6_3_1_0 := by decide
theorem sourceRowRotation6_3_1_1 : rotatedStateRow3 sourceState6_1_1 = stateRow6_3_1_1 := by decide
theorem sourceRowRotation6_3_1_2 : rotatedStateRow3 sourceState6_1_2 = stateRow6_3_1_2 := by decide
theorem sourceRowRotation6_3_1_3 : rotatedStateRow3 sourceState6_1_3 = stateRow6_3_1_3 := by decide
theorem sourceRowRotation6_3_1_4 : rotatedStateRow3 sourceState6_1_4 = stateRow6_3_1_4 := by decide
theorem sourceRowRotation6_3_1_5 : rotatedStateRow3 sourceState6_1_5 = stateRow6_3_1_5 := by decide
theorem sourceRowRotation6_3_1_6 : rotatedStateRow3 sourceState6_1_6 = stateRow6_3_1_6 := by decide
theorem sourceRowRotation6_3_1_7 : rotatedStateRow3 sourceState6_1_7 = stateRow6_3_1_7 := by decide
theorem sourceRowRotation6_3_1_8 : rotatedStateRow3 sourceState6_1_8 = stateRow6_3_1_8 := by decide
theorem sourceRowRotation6_3_1_9 : rotatedStateRow3 sourceState6_1_9 = stateRow6_3_1_9 := by decide
theorem sourceRowRotation6_3_1_10 : rotatedStateRow3 sourceState6_1_10 = stateRow6_3_1_10 := by decide
theorem sourceRowRotation6_3_1_11 : rotatedStateRow3 sourceState6_1_11 = stateRow6_3_1_11 := by decide
theorem initial6_3_1 : (source6_1).map (rotatePatch 3 (hexRegion 5)) = rows0_6_3_1.map Verdict.patch := by
  rw [sourceStates6_1, sourceStateSplit6_1, rotateCanonical_map3]
  simp only [List.map_cons, List.map_nil, sourceRowRotation6_3_1_0, sourceRowRotation6_3_1_1, sourceRowRotation6_3_1_2, sourceRowRotation6_3_1_3, sourceRowRotation6_3_1_4, sourceRowRotation6_3_1_5, sourceRowRotation6_3_1_6, sourceRowRotation6_3_1_7, sourceRowRotation6_3_1_8, sourceRowRotation6_3_1_9, sourceRowRotation6_3_1_10, sourceRowRotation6_3_1_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
