module

public import SpectreFinite.RadiusFivePruningBlock1T5C4Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation1_5_4_0 : rotatedStateRow5 sourceState1_4_0 = stateRow1_5_4_0 := by decide
theorem sourceRowRotation1_5_4_1 : rotatedStateRow5 sourceState1_4_1 = stateRow1_5_4_1 := by decide
theorem sourceRowRotation1_5_4_2 : rotatedStateRow5 sourceState1_4_2 = stateRow1_5_4_2 := by decide
theorem sourceRowRotation1_5_4_3 : rotatedStateRow5 sourceState1_4_3 = stateRow1_5_4_3 := by decide
theorem sourceRowRotation1_5_4_4 : rotatedStateRow5 sourceState1_4_4 = stateRow1_5_4_4 := by decide
theorem sourceRowRotation1_5_4_5 : rotatedStateRow5 sourceState1_4_5 = stateRow1_5_4_5 := by decide
theorem sourceRowRotation1_5_4_6 : rotatedStateRow5 sourceState1_4_6 = stateRow1_5_4_6 := by decide
theorem sourceRowRotation1_5_4_7 : rotatedStateRow5 sourceState1_4_7 = stateRow1_5_4_7 := by decide
theorem sourceRowRotation1_5_4_8 : rotatedStateRow5 sourceState1_4_8 = stateRow1_5_4_8 := by decide
theorem sourceRowRotation1_5_4_9 : rotatedStateRow5 sourceState1_4_9 = stateRow1_5_4_9 := by decide
theorem sourceRowRotation1_5_4_10 : rotatedStateRow5 sourceState1_4_10 = stateRow1_5_4_10 := by decide
theorem initial1_5_4 : (source1_4).map (rotatePatch 5 (hexRegion 5)) = rows0_1_5_4.map Verdict.patch := by
  rw [sourceStates1_4, sourceStateSplit1_4, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation1_5_4_0, sourceRowRotation1_5_4_1, sourceRowRotation1_5_4_2, sourceRowRotation1_5_4_3, sourceRowRotation1_5_4_4, sourceRowRotation1_5_4_5, sourceRowRotation1_5_4_6, sourceRowRotation1_5_4_7, sourceRowRotation1_5_4_8, sourceRowRotation1_5_4_9, sourceRowRotation1_5_4_10] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
