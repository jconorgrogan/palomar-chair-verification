module

public import SpectreFinite.RadiusFivePruningBlock8T0C5Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation8_0_5_0 : rotatedStateRow0 sourceState8_5_0 = stateRow8_0_5_0 := by decide
theorem sourceRowRotation8_0_5_1 : rotatedStateRow0 sourceState8_5_1 = stateRow8_0_5_1 := by decide
theorem sourceRowRotation8_0_5_2 : rotatedStateRow0 sourceState8_5_2 = stateRow8_0_5_2 := by decide
theorem sourceRowRotation8_0_5_3 : rotatedStateRow0 sourceState8_5_3 = stateRow8_0_5_3 := by decide
theorem sourceRowRotation8_0_5_4 : rotatedStateRow0 sourceState8_5_4 = stateRow8_0_5_4 := by decide
theorem sourceRowRotation8_0_5_5 : rotatedStateRow0 sourceState8_5_5 = stateRow8_0_5_5 := by decide
theorem sourceRowRotation8_0_5_6 : rotatedStateRow0 sourceState8_5_6 = stateRow8_0_5_6 := by decide
theorem sourceRowRotation8_0_5_7 : rotatedStateRow0 sourceState8_5_7 = stateRow8_0_5_7 := by decide
theorem sourceRowRotation8_0_5_8 : rotatedStateRow0 sourceState8_5_8 = stateRow8_0_5_8 := by decide
theorem sourceRowRotation8_0_5_9 : rotatedStateRow0 sourceState8_5_9 = stateRow8_0_5_9 := by decide
theorem initial8_0_5 : (source8_5).map (rotatePatch 0 (hexRegion 5)) = rows0_8_0_5.map Verdict.patch := by
  rw [sourceStates8_5, sourceStateSplit8_5, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation8_0_5_0, sourceRowRotation8_0_5_1, sourceRowRotation8_0_5_2, sourceRowRotation8_0_5_3, sourceRowRotation8_0_5_4, sourceRowRotation8_0_5_5, sourceRowRotation8_0_5_6, sourceRowRotation8_0_5_7, sourceRowRotation8_0_5_8, sourceRowRotation8_0_5_9] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
