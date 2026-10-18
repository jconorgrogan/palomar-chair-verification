module

public import SpectreFinite.RadiusFivePruningBlock8T4C4Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation8_4_4_0 : rotatedStateRow4 sourceState8_4_0 = stateRow8_4_4_0 := by decide
theorem sourceRowRotation8_4_4_1 : rotatedStateRow4 sourceState8_4_1 = stateRow8_4_4_1 := by decide
theorem sourceRowRotation8_4_4_2 : rotatedStateRow4 sourceState8_4_2 = stateRow8_4_4_2 := by decide
theorem sourceRowRotation8_4_4_3 : rotatedStateRow4 sourceState8_4_3 = stateRow8_4_4_3 := by decide
theorem sourceRowRotation8_4_4_4 : rotatedStateRow4 sourceState8_4_4 = stateRow8_4_4_4 := by decide
theorem sourceRowRotation8_4_4_5 : rotatedStateRow4 sourceState8_4_5 = stateRow8_4_4_5 := by decide
theorem sourceRowRotation8_4_4_6 : rotatedStateRow4 sourceState8_4_6 = stateRow8_4_4_6 := by decide
theorem sourceRowRotation8_4_4_7 : rotatedStateRow4 sourceState8_4_7 = stateRow8_4_4_7 := by decide
theorem sourceRowRotation8_4_4_8 : rotatedStateRow4 sourceState8_4_8 = stateRow8_4_4_8 := by decide
theorem sourceRowRotation8_4_4_9 : rotatedStateRow4 sourceState8_4_9 = stateRow8_4_4_9 := by decide
theorem sourceRowRotation8_4_4_10 : rotatedStateRow4 sourceState8_4_10 = stateRow8_4_4_10 := by decide
theorem sourceRowRotation8_4_4_11 : rotatedStateRow4 sourceState8_4_11 = stateRow8_4_4_11 := by decide
theorem initial8_4_4 : (source8_4).map (rotatePatch 4 (hexRegion 5)) = rows0_8_4_4.map Verdict.patch := by
  rw [sourceStates8_4, sourceStateSplit8_4, rotateCanonical_map4]
  simp only [List.map_cons, List.map_nil, sourceRowRotation8_4_4_0, sourceRowRotation8_4_4_1, sourceRowRotation8_4_4_2, sourceRowRotation8_4_4_3, sourceRowRotation8_4_4_4, sourceRowRotation8_4_4_5, sourceRowRotation8_4_4_6, sourceRowRotation8_4_4_7, sourceRowRotation8_4_4_8, sourceRowRotation8_4_4_9, sourceRowRotation8_4_4_10, sourceRowRotation8_4_4_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
