module

public import SpectreFinite.RadiusFivePruningBlock1T5C2Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation1_5_2_0 : rotatedStateRow5 sourceState1_2_0 = stateRow1_5_2_0 := by decide
theorem sourceRowRotation1_5_2_1 : rotatedStateRow5 sourceState1_2_1 = stateRow1_5_2_1 := by decide
theorem sourceRowRotation1_5_2_2 : rotatedStateRow5 sourceState1_2_2 = stateRow1_5_2_2 := by decide
theorem sourceRowRotation1_5_2_3 : rotatedStateRow5 sourceState1_2_3 = stateRow1_5_2_3 := by decide
theorem sourceRowRotation1_5_2_4 : rotatedStateRow5 sourceState1_2_4 = stateRow1_5_2_4 := by decide
theorem sourceRowRotation1_5_2_5 : rotatedStateRow5 sourceState1_2_5 = stateRow1_5_2_5 := by decide
theorem sourceRowRotation1_5_2_6 : rotatedStateRow5 sourceState1_2_6 = stateRow1_5_2_6 := by decide
theorem sourceRowRotation1_5_2_7 : rotatedStateRow5 sourceState1_2_7 = stateRow1_5_2_7 := by decide
theorem sourceRowRotation1_5_2_8 : rotatedStateRow5 sourceState1_2_8 = stateRow1_5_2_8 := by decide
theorem sourceRowRotation1_5_2_9 : rotatedStateRow5 sourceState1_2_9 = stateRow1_5_2_9 := by decide
theorem sourceRowRotation1_5_2_10 : rotatedStateRow5 sourceState1_2_10 = stateRow1_5_2_10 := by decide
theorem sourceRowRotation1_5_2_11 : rotatedStateRow5 sourceState1_2_11 = stateRow1_5_2_11 := by decide
theorem initial1_5_2 : (source1_2).map (rotatePatch 5 (hexRegion 5)) = rows0_1_5_2.map Verdict.patch := by
  rw [sourceStates1_2, sourceStateSplit1_2, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation1_5_2_0, sourceRowRotation1_5_2_1, sourceRowRotation1_5_2_2, sourceRowRotation1_5_2_3, sourceRowRotation1_5_2_4, sourceRowRotation1_5_2_5, sourceRowRotation1_5_2_6, sourceRowRotation1_5_2_7, sourceRowRotation1_5_2_8, sourceRowRotation1_5_2_9, sourceRowRotation1_5_2_10, sourceRowRotation1_5_2_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
