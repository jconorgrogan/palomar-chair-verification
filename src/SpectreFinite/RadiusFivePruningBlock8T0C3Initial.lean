module

public import SpectreFinite.RadiusFivePruningBlock8T0C3Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation8_0_3_0 : rotatedStateRow0 sourceState8_3_0 = stateRow8_0_3_0 := by decide
theorem sourceRowRotation8_0_3_1 : rotatedStateRow0 sourceState8_3_1 = stateRow8_0_3_1 := by decide
theorem sourceRowRotation8_0_3_2 : rotatedStateRow0 sourceState8_3_2 = stateRow8_0_3_2 := by decide
theorem sourceRowRotation8_0_3_3 : rotatedStateRow0 sourceState8_3_3 = stateRow8_0_3_3 := by decide
theorem sourceRowRotation8_0_3_4 : rotatedStateRow0 sourceState8_3_4 = stateRow8_0_3_4 := by decide
theorem sourceRowRotation8_0_3_5 : rotatedStateRow0 sourceState8_3_5 = stateRow8_0_3_5 := by decide
theorem sourceRowRotation8_0_3_6 : rotatedStateRow0 sourceState8_3_6 = stateRow8_0_3_6 := by decide
theorem sourceRowRotation8_0_3_7 : rotatedStateRow0 sourceState8_3_7 = stateRow8_0_3_7 := by decide
theorem sourceRowRotation8_0_3_8 : rotatedStateRow0 sourceState8_3_8 = stateRow8_0_3_8 := by decide
theorem sourceRowRotation8_0_3_9 : rotatedStateRow0 sourceState8_3_9 = stateRow8_0_3_9 := by decide
theorem sourceRowRotation8_0_3_10 : rotatedStateRow0 sourceState8_3_10 = stateRow8_0_3_10 := by decide
theorem sourceRowRotation8_0_3_11 : rotatedStateRow0 sourceState8_3_11 = stateRow8_0_3_11 := by decide
theorem initial8_0_3 : (source8_3).map (rotatePatch 0 (hexRegion 5)) = rows0_8_0_3.map Verdict.patch := by
  rw [sourceStates8_3, sourceStateSplit8_3, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation8_0_3_0, sourceRowRotation8_0_3_1, sourceRowRotation8_0_3_2, sourceRowRotation8_0_3_3, sourceRowRotation8_0_3_4, sourceRowRotation8_0_3_5, sourceRowRotation8_0_3_6, sourceRowRotation8_0_3_7, sourceRowRotation8_0_3_8, sourceRowRotation8_0_3_9, sourceRowRotation8_0_3_10, sourceRowRotation8_0_3_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
