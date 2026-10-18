module

public import SpectreFinite.RadiusFivePruningBlock4T5C1Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation4_5_1_0 : rotatedStateRow5 sourceState4_1_0 = stateRow4_5_1_0 := by decide
theorem sourceRowRotation4_5_1_1 : rotatedStateRow5 sourceState4_1_1 = stateRow4_5_1_1 := by decide
theorem sourceRowRotation4_5_1_2 : rotatedStateRow5 sourceState4_1_2 = stateRow4_5_1_2 := by decide
theorem sourceRowRotation4_5_1_3 : rotatedStateRow5 sourceState4_1_3 = stateRow4_5_1_3 := by decide
theorem sourceRowRotation4_5_1_4 : rotatedStateRow5 sourceState4_1_4 = stateRow4_5_1_4 := by decide
theorem sourceRowRotation4_5_1_5 : rotatedStateRow5 sourceState4_1_5 = stateRow4_5_1_5 := by decide
theorem sourceRowRotation4_5_1_6 : rotatedStateRow5 sourceState4_1_6 = stateRow4_5_1_6 := by decide
theorem sourceRowRotation4_5_1_7 : rotatedStateRow5 sourceState4_1_7 = stateRow4_5_1_7 := by decide
theorem sourceRowRotation4_5_1_8 : rotatedStateRow5 sourceState4_1_8 = stateRow4_5_1_8 := by decide
theorem sourceRowRotation4_5_1_9 : rotatedStateRow5 sourceState4_1_9 = stateRow4_5_1_9 := by decide
theorem sourceRowRotation4_5_1_10 : rotatedStateRow5 sourceState4_1_10 = stateRow4_5_1_10 := by decide
theorem sourceRowRotation4_5_1_11 : rotatedStateRow5 sourceState4_1_11 = stateRow4_5_1_11 := by decide
theorem initial4_5_1 : (source4_1).map (rotatePatch 5 (hexRegion 5)) = rows0_4_5_1.map Verdict.patch := by
  rw [sourceStates4_1, sourceStateSplit4_1, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation4_5_1_0, sourceRowRotation4_5_1_1, sourceRowRotation4_5_1_2, sourceRowRotation4_5_1_3, sourceRowRotation4_5_1_4, sourceRowRotation4_5_1_5, sourceRowRotation4_5_1_6, sourceRowRotation4_5_1_7, sourceRowRotation4_5_1_8, sourceRowRotation4_5_1_9, sourceRowRotation4_5_1_10, sourceRowRotation4_5_1_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
