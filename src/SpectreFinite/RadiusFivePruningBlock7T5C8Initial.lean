module

public import SpectreFinite.RadiusFivePruningBlock7T5C8Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation7_5_8_0 : rotatedStateRow5 sourceState7_8_0 = stateRow7_5_8_0 := by decide
theorem sourceRowRotation7_5_8_1 : rotatedStateRow5 sourceState7_8_1 = stateRow7_5_8_1 := by decide
theorem sourceRowRotation7_5_8_2 : rotatedStateRow5 sourceState7_8_2 = stateRow7_5_8_2 := by decide
theorem sourceRowRotation7_5_8_3 : rotatedStateRow5 sourceState7_8_3 = stateRow7_5_8_3 := by decide
theorem sourceRowRotation7_5_8_4 : rotatedStateRow5 sourceState7_8_4 = stateRow7_5_8_4 := by decide
theorem sourceRowRotation7_5_8_5 : rotatedStateRow5 sourceState7_8_5 = stateRow7_5_8_5 := by decide
theorem sourceRowRotation7_5_8_6 : rotatedStateRow5 sourceState7_8_6 = stateRow7_5_8_6 := by decide
theorem sourceRowRotation7_5_8_7 : rotatedStateRow5 sourceState7_8_7 = stateRow7_5_8_7 := by decide
theorem sourceRowRotation7_5_8_8 : rotatedStateRow5 sourceState7_8_8 = stateRow7_5_8_8 := by decide
theorem sourceRowRotation7_5_8_9 : rotatedStateRow5 sourceState7_8_9 = stateRow7_5_8_9 := by decide
theorem initial7_5_8 : (source7_8).map (rotatePatch 5 (hexRegion 5)) = rows0_7_5_8.map Verdict.patch := by
  rw [sourceStates7_8, sourceStateSplit7_8, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_5_8_0, sourceRowRotation7_5_8_1, sourceRowRotation7_5_8_2, sourceRowRotation7_5_8_3, sourceRowRotation7_5_8_4, sourceRowRotation7_5_8_5, sourceRowRotation7_5_8_6, sourceRowRotation7_5_8_7, sourceRowRotation7_5_8_8, sourceRowRotation7_5_8_9] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
