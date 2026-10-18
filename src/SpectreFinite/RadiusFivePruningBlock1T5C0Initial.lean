module

public import SpectreFinite.RadiusFivePruningBlock1T5C0Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation1_5_0_0 : rotatedStateRow5 sourceState1_0_0 = stateRow1_5_0_0 := by decide
theorem sourceRowRotation1_5_0_1 : rotatedStateRow5 sourceState1_0_1 = stateRow1_5_0_1 := by decide
theorem sourceRowRotation1_5_0_2 : rotatedStateRow5 sourceState1_0_2 = stateRow1_5_0_2 := by decide
theorem sourceRowRotation1_5_0_3 : rotatedStateRow5 sourceState1_0_3 = stateRow1_5_0_3 := by decide
theorem sourceRowRotation1_5_0_4 : rotatedStateRow5 sourceState1_0_4 = stateRow1_5_0_4 := by decide
theorem sourceRowRotation1_5_0_5 : rotatedStateRow5 sourceState1_0_5 = stateRow1_5_0_5 := by decide
theorem sourceRowRotation1_5_0_6 : rotatedStateRow5 sourceState1_0_6 = stateRow1_5_0_6 := by decide
theorem sourceRowRotation1_5_0_7 : rotatedStateRow5 sourceState1_0_7 = stateRow1_5_0_7 := by decide
theorem sourceRowRotation1_5_0_8 : rotatedStateRow5 sourceState1_0_8 = stateRow1_5_0_8 := by decide
theorem sourceRowRotation1_5_0_9 : rotatedStateRow5 sourceState1_0_9 = stateRow1_5_0_9 := by decide
theorem sourceRowRotation1_5_0_10 : rotatedStateRow5 sourceState1_0_10 = stateRow1_5_0_10 := by decide
theorem sourceRowRotation1_5_0_11 : rotatedStateRow5 sourceState1_0_11 = stateRow1_5_0_11 := by decide
theorem initial1_5_0 : (source1_0).map (rotatePatch 5 (hexRegion 5)) = rows0_1_5_0.map Verdict.patch := by
  rw [sourceStates1_0, sourceStateSplit1_0, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation1_5_0_0, sourceRowRotation1_5_0_1, sourceRowRotation1_5_0_2, sourceRowRotation1_5_0_3, sourceRowRotation1_5_0_4, sourceRowRotation1_5_0_5, sourceRowRotation1_5_0_6, sourceRowRotation1_5_0_7, sourceRowRotation1_5_0_8, sourceRowRotation1_5_0_9, sourceRowRotation1_5_0_10, sourceRowRotation1_5_0_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
