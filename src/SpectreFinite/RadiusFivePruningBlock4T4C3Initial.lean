module

public import SpectreFinite.RadiusFivePruningBlock4T4C3Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation4_4_3_0 : rotatedStateRow4 sourceState4_3_0 = stateRow4_4_3_0 := by decide
theorem sourceRowRotation4_4_3_1 : rotatedStateRow4 sourceState4_3_1 = stateRow4_4_3_1 := by decide
theorem sourceRowRotation4_4_3_2 : rotatedStateRow4 sourceState4_3_2 = stateRow4_4_3_2 := by decide
theorem sourceRowRotation4_4_3_3 : rotatedStateRow4 sourceState4_3_3 = stateRow4_4_3_3 := by decide
theorem sourceRowRotation4_4_3_4 : rotatedStateRow4 sourceState4_3_4 = stateRow4_4_3_4 := by decide
theorem sourceRowRotation4_4_3_5 : rotatedStateRow4 sourceState4_3_5 = stateRow4_4_3_5 := by decide
theorem sourceRowRotation4_4_3_6 : rotatedStateRow4 sourceState4_3_6 = stateRow4_4_3_6 := by decide
theorem sourceRowRotation4_4_3_7 : rotatedStateRow4 sourceState4_3_7 = stateRow4_4_3_7 := by decide
theorem sourceRowRotation4_4_3_8 : rotatedStateRow4 sourceState4_3_8 = stateRow4_4_3_8 := by decide
theorem sourceRowRotation4_4_3_9 : rotatedStateRow4 sourceState4_3_9 = stateRow4_4_3_9 := by decide
theorem sourceRowRotation4_4_3_10 : rotatedStateRow4 sourceState4_3_10 = stateRow4_4_3_10 := by decide
theorem initial4_4_3 : (source4_3).map (rotatePatch 4 (hexRegion 5)) = rows0_4_4_3.map Verdict.patch := by
  rw [sourceStates4_3, sourceStateSplit4_3, rotateCanonical_map4]
  simp only [List.map_cons, List.map_nil, sourceRowRotation4_4_3_0, sourceRowRotation4_4_3_1, sourceRowRotation4_4_3_2, sourceRowRotation4_4_3_3, sourceRowRotation4_4_3_4, sourceRowRotation4_4_3_5, sourceRowRotation4_4_3_6, sourceRowRotation4_4_3_7, sourceRowRotation4_4_3_8, sourceRowRotation4_4_3_9, sourceRowRotation4_4_3_10] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
