module

public import SpectreFinite.RadiusFivePruningBlock8T5C0Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation8_5_0_0 : rotatedStateRow5 sourceState8_0_0 = stateRow8_5_0_0 := by decide
theorem sourceRowRotation8_5_0_1 : rotatedStateRow5 sourceState8_0_1 = stateRow8_5_0_1 := by decide
theorem sourceRowRotation8_5_0_2 : rotatedStateRow5 sourceState8_0_2 = stateRow8_5_0_2 := by decide
theorem sourceRowRotation8_5_0_3 : rotatedStateRow5 sourceState8_0_3 = stateRow8_5_0_3 := by decide
theorem sourceRowRotation8_5_0_4 : rotatedStateRow5 sourceState8_0_4 = stateRow8_5_0_4 := by decide
theorem sourceRowRotation8_5_0_5 : rotatedStateRow5 sourceState8_0_5 = stateRow8_5_0_5 := by decide
theorem sourceRowRotation8_5_0_6 : rotatedStateRow5 sourceState8_0_6 = stateRow8_5_0_6 := by decide
theorem sourceRowRotation8_5_0_7 : rotatedStateRow5 sourceState8_0_7 = stateRow8_5_0_7 := by decide
theorem sourceRowRotation8_5_0_8 : rotatedStateRow5 sourceState8_0_8 = stateRow8_5_0_8 := by decide
theorem sourceRowRotation8_5_0_9 : rotatedStateRow5 sourceState8_0_9 = stateRow8_5_0_9 := by decide
theorem sourceRowRotation8_5_0_10 : rotatedStateRow5 sourceState8_0_10 = stateRow8_5_0_10 := by decide
theorem sourceRowRotation8_5_0_11 : rotatedStateRow5 sourceState8_0_11 = stateRow8_5_0_11 := by decide
theorem initial8_5_0 : (source8_0).map (rotatePatch 5 (hexRegion 5)) = rows0_8_5_0.map Verdict.patch := by
  rw [sourceStates8_0, sourceStateSplit8_0, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation8_5_0_0, sourceRowRotation8_5_0_1, sourceRowRotation8_5_0_2, sourceRowRotation8_5_0_3, sourceRowRotation8_5_0_4, sourceRowRotation8_5_0_5, sourceRowRotation8_5_0_6, sourceRowRotation8_5_0_7, sourceRowRotation8_5_0_8, sourceRowRotation8_5_0_9, sourceRowRotation8_5_0_10, sourceRowRotation8_5_0_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
