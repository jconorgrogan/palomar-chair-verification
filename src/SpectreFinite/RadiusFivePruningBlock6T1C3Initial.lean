module

public import SpectreFinite.RadiusFivePruningBlock6T1C3Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation6_1_3_0 : rotatedStateRow1 sourceState6_3_0 = stateRow6_1_3_0 := by decide
theorem sourceRowRotation6_1_3_1 : rotatedStateRow1 sourceState6_3_1 = stateRow6_1_3_1 := by decide
theorem sourceRowRotation6_1_3_2 : rotatedStateRow1 sourceState6_3_2 = stateRow6_1_3_2 := by decide
theorem sourceRowRotation6_1_3_3 : rotatedStateRow1 sourceState6_3_3 = stateRow6_1_3_3 := by decide
theorem sourceRowRotation6_1_3_4 : rotatedStateRow1 sourceState6_3_4 = stateRow6_1_3_4 := by decide
theorem sourceRowRotation6_1_3_5 : rotatedStateRow1 sourceState6_3_5 = stateRow6_1_3_5 := by decide
theorem sourceRowRotation6_1_3_6 : rotatedStateRow1 sourceState6_3_6 = stateRow6_1_3_6 := by decide
theorem sourceRowRotation6_1_3_7 : rotatedStateRow1 sourceState6_3_7 = stateRow6_1_3_7 := by decide
theorem sourceRowRotation6_1_3_8 : rotatedStateRow1 sourceState6_3_8 = stateRow6_1_3_8 := by decide
theorem sourceRowRotation6_1_3_9 : rotatedStateRow1 sourceState6_3_9 = stateRow6_1_3_9 := by decide
theorem sourceRowRotation6_1_3_10 : rotatedStateRow1 sourceState6_3_10 = stateRow6_1_3_10 := by decide
theorem sourceRowRotation6_1_3_11 : rotatedStateRow1 sourceState6_3_11 = stateRow6_1_3_11 := by decide
theorem initial6_1_3 : (source6_3).map (rotatePatch 1 (hexRegion 5)) = rows0_6_1_3.map Verdict.patch := by
  rw [sourceStates6_3, sourceStateSplit6_3, rotateCanonical_map1]
  simp only [List.map_cons, List.map_nil, sourceRowRotation6_1_3_0, sourceRowRotation6_1_3_1, sourceRowRotation6_1_3_2, sourceRowRotation6_1_3_3, sourceRowRotation6_1_3_4, sourceRowRotation6_1_3_5, sourceRowRotation6_1_3_6, sourceRowRotation6_1_3_7, sourceRowRotation6_1_3_8, sourceRowRotation6_1_3_9, sourceRowRotation6_1_3_10, sourceRowRotation6_1_3_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
