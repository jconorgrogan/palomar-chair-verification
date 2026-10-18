module

public import SpectreFinite.RadiusFivePruningBlock8T4C3Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation8_4_3_0 : rotatedStateRow4 sourceState8_3_0 = stateRow8_4_3_0 := by decide
theorem sourceRowRotation8_4_3_1 : rotatedStateRow4 sourceState8_3_1 = stateRow8_4_3_1 := by decide
theorem sourceRowRotation8_4_3_2 : rotatedStateRow4 sourceState8_3_2 = stateRow8_4_3_2 := by decide
theorem sourceRowRotation8_4_3_3 : rotatedStateRow4 sourceState8_3_3 = stateRow8_4_3_3 := by decide
theorem sourceRowRotation8_4_3_4 : rotatedStateRow4 sourceState8_3_4 = stateRow8_4_3_4 := by decide
theorem sourceRowRotation8_4_3_5 : rotatedStateRow4 sourceState8_3_5 = stateRow8_4_3_5 := by decide
theorem sourceRowRotation8_4_3_6 : rotatedStateRow4 sourceState8_3_6 = stateRow8_4_3_6 := by decide
theorem sourceRowRotation8_4_3_7 : rotatedStateRow4 sourceState8_3_7 = stateRow8_4_3_7 := by decide
theorem sourceRowRotation8_4_3_8 : rotatedStateRow4 sourceState8_3_8 = stateRow8_4_3_8 := by decide
theorem sourceRowRotation8_4_3_9 : rotatedStateRow4 sourceState8_3_9 = stateRow8_4_3_9 := by decide
theorem sourceRowRotation8_4_3_10 : rotatedStateRow4 sourceState8_3_10 = stateRow8_4_3_10 := by decide
theorem sourceRowRotation8_4_3_11 : rotatedStateRow4 sourceState8_3_11 = stateRow8_4_3_11 := by decide
theorem initial8_4_3 : (source8_3).map (rotatePatch 4 (hexRegion 5)) = rows0_8_4_3.map Verdict.patch := by
  rw [sourceStates8_3, sourceStateSplit8_3, rotateCanonical_map4]
  simp only [List.map_cons, List.map_nil, sourceRowRotation8_4_3_0, sourceRowRotation8_4_3_1, sourceRowRotation8_4_3_2, sourceRowRotation8_4_3_3, sourceRowRotation8_4_3_4, sourceRowRotation8_4_3_5, sourceRowRotation8_4_3_6, sourceRowRotation8_4_3_7, sourceRowRotation8_4_3_8, sourceRowRotation8_4_3_9, sourceRowRotation8_4_3_10, sourceRowRotation8_4_3_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
