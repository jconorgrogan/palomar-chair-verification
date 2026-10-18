module

public import SpectreFinite.RadiusFivePruningBlock6T0C2Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation6_0_2_0 : rotatedStateRow0 sourceState6_2_0 = stateRow6_0_2_0 := by decide
theorem sourceRowRotation6_0_2_1 : rotatedStateRow0 sourceState6_2_1 = stateRow6_0_2_1 := by decide
theorem sourceRowRotation6_0_2_2 : rotatedStateRow0 sourceState6_2_2 = stateRow6_0_2_2 := by decide
theorem sourceRowRotation6_0_2_3 : rotatedStateRow0 sourceState6_2_3 = stateRow6_0_2_3 := by decide
theorem sourceRowRotation6_0_2_4 : rotatedStateRow0 sourceState6_2_4 = stateRow6_0_2_4 := by decide
theorem sourceRowRotation6_0_2_5 : rotatedStateRow0 sourceState6_2_5 = stateRow6_0_2_5 := by decide
theorem sourceRowRotation6_0_2_6 : rotatedStateRow0 sourceState6_2_6 = stateRow6_0_2_6 := by decide
theorem sourceRowRotation6_0_2_7 : rotatedStateRow0 sourceState6_2_7 = stateRow6_0_2_7 := by decide
theorem sourceRowRotation6_0_2_8 : rotatedStateRow0 sourceState6_2_8 = stateRow6_0_2_8 := by decide
theorem sourceRowRotation6_0_2_9 : rotatedStateRow0 sourceState6_2_9 = stateRow6_0_2_9 := by decide
theorem sourceRowRotation6_0_2_10 : rotatedStateRow0 sourceState6_2_10 = stateRow6_0_2_10 := by decide
theorem sourceRowRotation6_0_2_11 : rotatedStateRow0 sourceState6_2_11 = stateRow6_0_2_11 := by decide
theorem initial6_0_2 : (source6_2).map (rotatePatch 0 (hexRegion 5)) = rows0_6_0_2.map Verdict.patch := by
  rw [sourceStates6_2, sourceStateSplit6_2, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation6_0_2_0, sourceRowRotation6_0_2_1, sourceRowRotation6_0_2_2, sourceRowRotation6_0_2_3, sourceRowRotation6_0_2_4, sourceRowRotation6_0_2_5, sourceRowRotation6_0_2_6, sourceRowRotation6_0_2_7, sourceRowRotation6_0_2_8, sourceRowRotation6_0_2_9, sourceRowRotation6_0_2_10, sourceRowRotation6_0_2_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
