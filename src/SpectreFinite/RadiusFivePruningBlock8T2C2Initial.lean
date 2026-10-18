module

public import SpectreFinite.RadiusFivePruningBlock8T2C2Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation8_2_2_0 : rotatedStateRow2 sourceState8_2_0 = stateRow8_2_2_0 := by decide
theorem sourceRowRotation8_2_2_1 : rotatedStateRow2 sourceState8_2_1 = stateRow8_2_2_1 := by decide
theorem sourceRowRotation8_2_2_2 : rotatedStateRow2 sourceState8_2_2 = stateRow8_2_2_2 := by decide
theorem sourceRowRotation8_2_2_3 : rotatedStateRow2 sourceState8_2_3 = stateRow8_2_2_3 := by decide
theorem sourceRowRotation8_2_2_4 : rotatedStateRow2 sourceState8_2_4 = stateRow8_2_2_4 := by decide
theorem sourceRowRotation8_2_2_5 : rotatedStateRow2 sourceState8_2_5 = stateRow8_2_2_5 := by decide
theorem sourceRowRotation8_2_2_6 : rotatedStateRow2 sourceState8_2_6 = stateRow8_2_2_6 := by decide
theorem sourceRowRotation8_2_2_7 : rotatedStateRow2 sourceState8_2_7 = stateRow8_2_2_7 := by decide
theorem sourceRowRotation8_2_2_8 : rotatedStateRow2 sourceState8_2_8 = stateRow8_2_2_8 := by decide
theorem sourceRowRotation8_2_2_9 : rotatedStateRow2 sourceState8_2_9 = stateRow8_2_2_9 := by decide
theorem sourceRowRotation8_2_2_10 : rotatedStateRow2 sourceState8_2_10 = stateRow8_2_2_10 := by decide
theorem sourceRowRotation8_2_2_11 : rotatedStateRow2 sourceState8_2_11 = stateRow8_2_2_11 := by decide
theorem initial8_2_2 : (source8_2).map (rotatePatch 2 (hexRegion 5)) = rows0_8_2_2.map Verdict.patch := by
  rw [sourceStates8_2, sourceStateSplit8_2, rotateCanonical_map2]
  simp only [List.map_cons, List.map_nil, sourceRowRotation8_2_2_0, sourceRowRotation8_2_2_1, sourceRowRotation8_2_2_2, sourceRowRotation8_2_2_3, sourceRowRotation8_2_2_4, sourceRowRotation8_2_2_5, sourceRowRotation8_2_2_6, sourceRowRotation8_2_2_7, sourceRowRotation8_2_2_8, sourceRowRotation8_2_2_9, sourceRowRotation8_2_2_10, sourceRowRotation8_2_2_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
