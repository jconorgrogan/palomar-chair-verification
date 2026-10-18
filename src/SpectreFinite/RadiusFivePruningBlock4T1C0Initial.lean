module

public import SpectreFinite.RadiusFivePruningBlock4T1C0Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation4_1_0_0 : rotatedStateRow1 sourceState4_0_0 = stateRow4_1_0_0 := by decide
theorem sourceRowRotation4_1_0_1 : rotatedStateRow1 sourceState4_0_1 = stateRow4_1_0_1 := by decide
theorem sourceRowRotation4_1_0_2 : rotatedStateRow1 sourceState4_0_2 = stateRow4_1_0_2 := by decide
theorem sourceRowRotation4_1_0_3 : rotatedStateRow1 sourceState4_0_3 = stateRow4_1_0_3 := by decide
theorem sourceRowRotation4_1_0_4 : rotatedStateRow1 sourceState4_0_4 = stateRow4_1_0_4 := by decide
theorem sourceRowRotation4_1_0_5 : rotatedStateRow1 sourceState4_0_5 = stateRow4_1_0_5 := by decide
theorem sourceRowRotation4_1_0_6 : rotatedStateRow1 sourceState4_0_6 = stateRow4_1_0_6 := by decide
theorem sourceRowRotation4_1_0_7 : rotatedStateRow1 sourceState4_0_7 = stateRow4_1_0_7 := by decide
theorem sourceRowRotation4_1_0_8 : rotatedStateRow1 sourceState4_0_8 = stateRow4_1_0_8 := by decide
theorem sourceRowRotation4_1_0_9 : rotatedStateRow1 sourceState4_0_9 = stateRow4_1_0_9 := by decide
theorem sourceRowRotation4_1_0_10 : rotatedStateRow1 sourceState4_0_10 = stateRow4_1_0_10 := by decide
theorem sourceRowRotation4_1_0_11 : rotatedStateRow1 sourceState4_0_11 = stateRow4_1_0_11 := by decide
theorem initial4_1_0 : (source4_0).map (rotatePatch 1 (hexRegion 5)) = rows0_4_1_0.map Verdict.patch := by
  rw [sourceStates4_0, sourceStateSplit4_0, rotateCanonical_map1]
  simp only [List.map_cons, List.map_nil, sourceRowRotation4_1_0_0, sourceRowRotation4_1_0_1, sourceRowRotation4_1_0_2, sourceRowRotation4_1_0_3, sourceRowRotation4_1_0_4, sourceRowRotation4_1_0_5, sourceRowRotation4_1_0_6, sourceRowRotation4_1_0_7, sourceRowRotation4_1_0_8, sourceRowRotation4_1_0_9, sourceRowRotation4_1_0_10, sourceRowRotation4_1_0_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
