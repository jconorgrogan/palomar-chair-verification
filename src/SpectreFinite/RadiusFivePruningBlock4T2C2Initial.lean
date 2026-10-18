module

public import SpectreFinite.RadiusFivePruningBlock4T2C2Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation4_2_2_0 : rotatedStateRow2 sourceState4_2_0 = stateRow4_2_2_0 := by decide
theorem sourceRowRotation4_2_2_1 : rotatedStateRow2 sourceState4_2_1 = stateRow4_2_2_1 := by decide
theorem sourceRowRotation4_2_2_2 : rotatedStateRow2 sourceState4_2_2 = stateRow4_2_2_2 := by decide
theorem sourceRowRotation4_2_2_3 : rotatedStateRow2 sourceState4_2_3 = stateRow4_2_2_3 := by decide
theorem sourceRowRotation4_2_2_4 : rotatedStateRow2 sourceState4_2_4 = stateRow4_2_2_4 := by decide
theorem sourceRowRotation4_2_2_5 : rotatedStateRow2 sourceState4_2_5 = stateRow4_2_2_5 := by decide
theorem sourceRowRotation4_2_2_6 : rotatedStateRow2 sourceState4_2_6 = stateRow4_2_2_6 := by decide
theorem sourceRowRotation4_2_2_7 : rotatedStateRow2 sourceState4_2_7 = stateRow4_2_2_7 := by decide
theorem sourceRowRotation4_2_2_8 : rotatedStateRow2 sourceState4_2_8 = stateRow4_2_2_8 := by decide
theorem sourceRowRotation4_2_2_9 : rotatedStateRow2 sourceState4_2_9 = stateRow4_2_2_9 := by decide
theorem sourceRowRotation4_2_2_10 : rotatedStateRow2 sourceState4_2_10 = stateRow4_2_2_10 := by decide
theorem sourceRowRotation4_2_2_11 : rotatedStateRow2 sourceState4_2_11 = stateRow4_2_2_11 := by decide
theorem initial4_2_2 : (source4_2).map (rotatePatch 2 (hexRegion 5)) = rows0_4_2_2.map Verdict.patch := by
  rw [sourceStates4_2, sourceStateSplit4_2, rotateCanonical_map2]
  simp only [List.map_cons, List.map_nil, sourceRowRotation4_2_2_0, sourceRowRotation4_2_2_1, sourceRowRotation4_2_2_2, sourceRowRotation4_2_2_3, sourceRowRotation4_2_2_4, sourceRowRotation4_2_2_5, sourceRowRotation4_2_2_6, sourceRowRotation4_2_2_7, sourceRowRotation4_2_2_8, sourceRowRotation4_2_2_9, sourceRowRotation4_2_2_10, sourceRowRotation4_2_2_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
