module

public import SpectreFinite.RadiusFivePruningBlock1T0C0Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation1_0_0_0 : rotatedStateRow0 sourceState1_0_0 = stateRow1_0_0_0 := by decide
theorem sourceRowRotation1_0_0_1 : rotatedStateRow0 sourceState1_0_1 = stateRow1_0_0_1 := by decide
theorem sourceRowRotation1_0_0_2 : rotatedStateRow0 sourceState1_0_2 = stateRow1_0_0_2 := by decide
theorem sourceRowRotation1_0_0_3 : rotatedStateRow0 sourceState1_0_3 = stateRow1_0_0_3 := by decide
theorem sourceRowRotation1_0_0_4 : rotatedStateRow0 sourceState1_0_4 = stateRow1_0_0_4 := by decide
theorem sourceRowRotation1_0_0_5 : rotatedStateRow0 sourceState1_0_5 = stateRow1_0_0_5 := by decide
theorem sourceRowRotation1_0_0_6 : rotatedStateRow0 sourceState1_0_6 = stateRow1_0_0_6 := by decide
theorem sourceRowRotation1_0_0_7 : rotatedStateRow0 sourceState1_0_7 = stateRow1_0_0_7 := by decide
theorem sourceRowRotation1_0_0_8 : rotatedStateRow0 sourceState1_0_8 = stateRow1_0_0_8 := by decide
theorem sourceRowRotation1_0_0_9 : rotatedStateRow0 sourceState1_0_9 = stateRow1_0_0_9 := by decide
theorem sourceRowRotation1_0_0_10 : rotatedStateRow0 sourceState1_0_10 = stateRow1_0_0_10 := by decide
theorem sourceRowRotation1_0_0_11 : rotatedStateRow0 sourceState1_0_11 = stateRow1_0_0_11 := by decide
theorem initial1_0_0 : (source1_0).map (rotatePatch 0 (hexRegion 5)) = rows0_1_0_0.map Verdict.patch := by
  rw [sourceStates1_0, sourceStateSplit1_0, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation1_0_0_0, sourceRowRotation1_0_0_1, sourceRowRotation1_0_0_2, sourceRowRotation1_0_0_3, sourceRowRotation1_0_0_4, sourceRowRotation1_0_0_5, sourceRowRotation1_0_0_6, sourceRowRotation1_0_0_7, sourceRowRotation1_0_0_8, sourceRowRotation1_0_0_9, sourceRowRotation1_0_0_10, sourceRowRotation1_0_0_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
