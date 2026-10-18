module

public import SpectreFinite.RadiusFivePruningBlock1T0C3Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation1_0_3_0 : rotatedStateRow0 sourceState1_3_0 = stateRow1_0_3_0 := by decide
theorem sourceRowRotation1_0_3_1 : rotatedStateRow0 sourceState1_3_1 = stateRow1_0_3_1 := by decide
theorem sourceRowRotation1_0_3_2 : rotatedStateRow0 sourceState1_3_2 = stateRow1_0_3_2 := by decide
theorem sourceRowRotation1_0_3_3 : rotatedStateRow0 sourceState1_3_3 = stateRow1_0_3_3 := by decide
theorem sourceRowRotation1_0_3_4 : rotatedStateRow0 sourceState1_3_4 = stateRow1_0_3_4 := by decide
theorem sourceRowRotation1_0_3_5 : rotatedStateRow0 sourceState1_3_5 = stateRow1_0_3_5 := by decide
theorem sourceRowRotation1_0_3_6 : rotatedStateRow0 sourceState1_3_6 = stateRow1_0_3_6 := by decide
theorem sourceRowRotation1_0_3_7 : rotatedStateRow0 sourceState1_3_7 = stateRow1_0_3_7 := by decide
theorem sourceRowRotation1_0_3_8 : rotatedStateRow0 sourceState1_3_8 = stateRow1_0_3_8 := by decide
theorem sourceRowRotation1_0_3_9 : rotatedStateRow0 sourceState1_3_9 = stateRow1_0_3_9 := by decide
theorem sourceRowRotation1_0_3_10 : rotatedStateRow0 sourceState1_3_10 = stateRow1_0_3_10 := by decide
theorem sourceRowRotation1_0_3_11 : rotatedStateRow0 sourceState1_3_11 = stateRow1_0_3_11 := by decide
theorem initial1_0_3 : (source1_3).map (rotatePatch 0 (hexRegion 5)) = rows0_1_0_3.map Verdict.patch := by
  rw [sourceStates1_3, sourceStateSplit1_3, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation1_0_3_0, sourceRowRotation1_0_3_1, sourceRowRotation1_0_3_2, sourceRowRotation1_0_3_3, sourceRowRotation1_0_3_4, sourceRowRotation1_0_3_5, sourceRowRotation1_0_3_6, sourceRowRotation1_0_3_7, sourceRowRotation1_0_3_8, sourceRowRotation1_0_3_9, sourceRowRotation1_0_3_10, sourceRowRotation1_0_3_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
