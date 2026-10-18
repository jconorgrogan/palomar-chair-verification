module

public import SpectreFinite.RadiusFivePruningBlock8T4C1Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation8_4_1_0 : rotatedStateRow4 sourceState8_1_0 = stateRow8_4_1_0 := by decide
theorem sourceRowRotation8_4_1_1 : rotatedStateRow4 sourceState8_1_1 = stateRow8_4_1_1 := by decide
theorem sourceRowRotation8_4_1_2 : rotatedStateRow4 sourceState8_1_2 = stateRow8_4_1_2 := by decide
theorem sourceRowRotation8_4_1_3 : rotatedStateRow4 sourceState8_1_3 = stateRow8_4_1_3 := by decide
theorem sourceRowRotation8_4_1_4 : rotatedStateRow4 sourceState8_1_4 = stateRow8_4_1_4 := by decide
theorem sourceRowRotation8_4_1_5 : rotatedStateRow4 sourceState8_1_5 = stateRow8_4_1_5 := by decide
theorem sourceRowRotation8_4_1_6 : rotatedStateRow4 sourceState8_1_6 = stateRow8_4_1_6 := by decide
theorem sourceRowRotation8_4_1_7 : rotatedStateRow4 sourceState8_1_7 = stateRow8_4_1_7 := by decide
theorem sourceRowRotation8_4_1_8 : rotatedStateRow4 sourceState8_1_8 = stateRow8_4_1_8 := by decide
theorem sourceRowRotation8_4_1_9 : rotatedStateRow4 sourceState8_1_9 = stateRow8_4_1_9 := by decide
theorem sourceRowRotation8_4_1_10 : rotatedStateRow4 sourceState8_1_10 = stateRow8_4_1_10 := by decide
theorem sourceRowRotation8_4_1_11 : rotatedStateRow4 sourceState8_1_11 = stateRow8_4_1_11 := by decide
theorem initial8_4_1 : (source8_1).map (rotatePatch 4 (hexRegion 5)) = rows0_8_4_1.map Verdict.patch := by
  rw [sourceStates8_1, sourceStateSplit8_1, rotateCanonical_map4]
  simp only [List.map_cons, List.map_nil, sourceRowRotation8_4_1_0, sourceRowRotation8_4_1_1, sourceRowRotation8_4_1_2, sourceRowRotation8_4_1_3, sourceRowRotation8_4_1_4, sourceRowRotation8_4_1_5, sourceRowRotation8_4_1_6, sourceRowRotation8_4_1_7, sourceRowRotation8_4_1_8, sourceRowRotation8_4_1_9, sourceRowRotation8_4_1_10, sourceRowRotation8_4_1_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
