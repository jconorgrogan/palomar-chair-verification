module

public import SpectreFinite.RadiusFivePruningBlock6T3C4Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation6_3_4_0 : rotatedStateRow3 sourceState6_4_0 = stateRow6_3_4_0 := by decide
theorem sourceRowRotation6_3_4_1 : rotatedStateRow3 sourceState6_4_1 = stateRow6_3_4_1 := by decide
theorem sourceRowRotation6_3_4_2 : rotatedStateRow3 sourceState6_4_2 = stateRow6_3_4_2 := by decide
theorem sourceRowRotation6_3_4_3 : rotatedStateRow3 sourceState6_4_3 = stateRow6_3_4_3 := by decide
theorem sourceRowRotation6_3_4_4 : rotatedStateRow3 sourceState6_4_4 = stateRow6_3_4_4 := by decide
theorem sourceRowRotation6_3_4_5 : rotatedStateRow3 sourceState6_4_5 = stateRow6_3_4_5 := by decide
theorem sourceRowRotation6_3_4_6 : rotatedStateRow3 sourceState6_4_6 = stateRow6_3_4_6 := by decide
theorem sourceRowRotation6_3_4_7 : rotatedStateRow3 sourceState6_4_7 = stateRow6_3_4_7 := by decide
theorem sourceRowRotation6_3_4_8 : rotatedStateRow3 sourceState6_4_8 = stateRow6_3_4_8 := by decide
theorem sourceRowRotation6_3_4_9 : rotatedStateRow3 sourceState6_4_9 = stateRow6_3_4_9 := by decide
theorem sourceRowRotation6_3_4_10 : rotatedStateRow3 sourceState6_4_10 = stateRow6_3_4_10 := by decide
theorem sourceRowRotation6_3_4_11 : rotatedStateRow3 sourceState6_4_11 = stateRow6_3_4_11 := by decide
theorem initial6_3_4 : (source6_4).map (rotatePatch 3 (hexRegion 5)) = rows0_6_3_4.map Verdict.patch := by
  rw [sourceStates6_4, sourceStateSplit6_4, rotateCanonical_map3]
  simp only [List.map_cons, List.map_nil, sourceRowRotation6_3_4_0, sourceRowRotation6_3_4_1, sourceRowRotation6_3_4_2, sourceRowRotation6_3_4_3, sourceRowRotation6_3_4_4, sourceRowRotation6_3_4_5, sourceRowRotation6_3_4_6, sourceRowRotation6_3_4_7, sourceRowRotation6_3_4_8, sourceRowRotation6_3_4_9, sourceRowRotation6_3_4_10, sourceRowRotation6_3_4_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
