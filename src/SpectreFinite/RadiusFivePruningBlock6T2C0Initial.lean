module

public import SpectreFinite.RadiusFivePruningBlock6T2C0Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation6_2_0_0 : rotatedStateRow2 sourceState6_0_0 = stateRow6_2_0_0 := by decide
theorem sourceRowRotation6_2_0_1 : rotatedStateRow2 sourceState6_0_1 = stateRow6_2_0_1 := by decide
theorem sourceRowRotation6_2_0_2 : rotatedStateRow2 sourceState6_0_2 = stateRow6_2_0_2 := by decide
theorem sourceRowRotation6_2_0_3 : rotatedStateRow2 sourceState6_0_3 = stateRow6_2_0_3 := by decide
theorem sourceRowRotation6_2_0_4 : rotatedStateRow2 sourceState6_0_4 = stateRow6_2_0_4 := by decide
theorem sourceRowRotation6_2_0_5 : rotatedStateRow2 sourceState6_0_5 = stateRow6_2_0_5 := by decide
theorem sourceRowRotation6_2_0_6 : rotatedStateRow2 sourceState6_0_6 = stateRow6_2_0_6 := by decide
theorem sourceRowRotation6_2_0_7 : rotatedStateRow2 sourceState6_0_7 = stateRow6_2_0_7 := by decide
theorem sourceRowRotation6_2_0_8 : rotatedStateRow2 sourceState6_0_8 = stateRow6_2_0_8 := by decide
theorem sourceRowRotation6_2_0_9 : rotatedStateRow2 sourceState6_0_9 = stateRow6_2_0_9 := by decide
theorem sourceRowRotation6_2_0_10 : rotatedStateRow2 sourceState6_0_10 = stateRow6_2_0_10 := by decide
theorem sourceRowRotation6_2_0_11 : rotatedStateRow2 sourceState6_0_11 = stateRow6_2_0_11 := by decide
theorem initial6_2_0 : (source6_0).map (rotatePatch 2 (hexRegion 5)) = rows0_6_2_0.map Verdict.patch := by
  rw [sourceStates6_0, sourceStateSplit6_0, rotateCanonical_map2]
  simp only [List.map_cons, List.map_nil, sourceRowRotation6_2_0_0, sourceRowRotation6_2_0_1, sourceRowRotation6_2_0_2, sourceRowRotation6_2_0_3, sourceRowRotation6_2_0_4, sourceRowRotation6_2_0_5, sourceRowRotation6_2_0_6, sourceRowRotation6_2_0_7, sourceRowRotation6_2_0_8, sourceRowRotation6_2_0_9, sourceRowRotation6_2_0_10, sourceRowRotation6_2_0_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
