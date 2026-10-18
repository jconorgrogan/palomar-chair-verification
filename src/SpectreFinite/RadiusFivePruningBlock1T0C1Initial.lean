module

public import SpectreFinite.RadiusFivePruningBlock1T0C1Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation1_0_1_0 : rotatedStateRow0 sourceState1_1_0 = stateRow1_0_1_0 := by decide
theorem sourceRowRotation1_0_1_1 : rotatedStateRow0 sourceState1_1_1 = stateRow1_0_1_1 := by decide
theorem sourceRowRotation1_0_1_2 : rotatedStateRow0 sourceState1_1_2 = stateRow1_0_1_2 := by decide
theorem sourceRowRotation1_0_1_3 : rotatedStateRow0 sourceState1_1_3 = stateRow1_0_1_3 := by decide
theorem sourceRowRotation1_0_1_4 : rotatedStateRow0 sourceState1_1_4 = stateRow1_0_1_4 := by decide
theorem sourceRowRotation1_0_1_5 : rotatedStateRow0 sourceState1_1_5 = stateRow1_0_1_5 := by decide
theorem sourceRowRotation1_0_1_6 : rotatedStateRow0 sourceState1_1_6 = stateRow1_0_1_6 := by decide
theorem sourceRowRotation1_0_1_7 : rotatedStateRow0 sourceState1_1_7 = stateRow1_0_1_7 := by decide
theorem sourceRowRotation1_0_1_8 : rotatedStateRow0 sourceState1_1_8 = stateRow1_0_1_8 := by decide
theorem sourceRowRotation1_0_1_9 : rotatedStateRow0 sourceState1_1_9 = stateRow1_0_1_9 := by decide
theorem sourceRowRotation1_0_1_10 : rotatedStateRow0 sourceState1_1_10 = stateRow1_0_1_10 := by decide
theorem sourceRowRotation1_0_1_11 : rotatedStateRow0 sourceState1_1_11 = stateRow1_0_1_11 := by decide
theorem initial1_0_1 : (source1_1).map (rotatePatch 0 (hexRegion 5)) = rows0_1_0_1.map Verdict.patch := by
  rw [sourceStates1_1, sourceStateSplit1_1, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation1_0_1_0, sourceRowRotation1_0_1_1, sourceRowRotation1_0_1_2, sourceRowRotation1_0_1_3, sourceRowRotation1_0_1_4, sourceRowRotation1_0_1_5, sourceRowRotation1_0_1_6, sourceRowRotation1_0_1_7, sourceRowRotation1_0_1_8, sourceRowRotation1_0_1_9, sourceRowRotation1_0_1_10, sourceRowRotation1_0_1_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
