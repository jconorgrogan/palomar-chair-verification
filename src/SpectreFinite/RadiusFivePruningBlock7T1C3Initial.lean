module

public import SpectreFinite.RadiusFivePruningBlock7T1C3Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation7_1_3_0 : rotatedStateRow1 sourceState7_3_0 = stateRow7_1_3_0 := by decide
theorem sourceRowRotation7_1_3_1 : rotatedStateRow1 sourceState7_3_1 = stateRow7_1_3_1 := by decide
theorem sourceRowRotation7_1_3_2 : rotatedStateRow1 sourceState7_3_2 = stateRow7_1_3_2 := by decide
theorem sourceRowRotation7_1_3_3 : rotatedStateRow1 sourceState7_3_3 = stateRow7_1_3_3 := by decide
theorem sourceRowRotation7_1_3_4 : rotatedStateRow1 sourceState7_3_4 = stateRow7_1_3_4 := by decide
theorem sourceRowRotation7_1_3_5 : rotatedStateRow1 sourceState7_3_5 = stateRow7_1_3_5 := by decide
theorem sourceRowRotation7_1_3_6 : rotatedStateRow1 sourceState7_3_6 = stateRow7_1_3_6 := by decide
theorem sourceRowRotation7_1_3_7 : rotatedStateRow1 sourceState7_3_7 = stateRow7_1_3_7 := by decide
theorem sourceRowRotation7_1_3_8 : rotatedStateRow1 sourceState7_3_8 = stateRow7_1_3_8 := by decide
theorem sourceRowRotation7_1_3_9 : rotatedStateRow1 sourceState7_3_9 = stateRow7_1_3_9 := by decide
theorem sourceRowRotation7_1_3_10 : rotatedStateRow1 sourceState7_3_10 = stateRow7_1_3_10 := by decide
theorem sourceRowRotation7_1_3_11 : rotatedStateRow1 sourceState7_3_11 = stateRow7_1_3_11 := by decide
theorem initial7_1_3 : (source7_3).map (rotatePatch 1 (hexRegion 5)) = rows0_7_1_3.map Verdict.patch := by
  rw [sourceStates7_3, sourceStateSplit7_3, rotateCanonical_map1]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_1_3_0, sourceRowRotation7_1_3_1, sourceRowRotation7_1_3_2, sourceRowRotation7_1_3_3, sourceRowRotation7_1_3_4, sourceRowRotation7_1_3_5, sourceRowRotation7_1_3_6, sourceRowRotation7_1_3_7, sourceRowRotation7_1_3_8, sourceRowRotation7_1_3_9, sourceRowRotation7_1_3_10, sourceRowRotation7_1_3_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
