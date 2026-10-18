module

public import SpectreFinite.RadiusFivePruningBlock7T2C1Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation7_2_1_0 : rotatedStateRow2 sourceState7_1_0 = stateRow7_2_1_0 := by decide
theorem sourceRowRotation7_2_1_1 : rotatedStateRow2 sourceState7_1_1 = stateRow7_2_1_1 := by decide
theorem sourceRowRotation7_2_1_2 : rotatedStateRow2 sourceState7_1_2 = stateRow7_2_1_2 := by decide
theorem sourceRowRotation7_2_1_3 : rotatedStateRow2 sourceState7_1_3 = stateRow7_2_1_3 := by decide
theorem sourceRowRotation7_2_1_4 : rotatedStateRow2 sourceState7_1_4 = stateRow7_2_1_4 := by decide
theorem sourceRowRotation7_2_1_5 : rotatedStateRow2 sourceState7_1_5 = stateRow7_2_1_5 := by decide
theorem sourceRowRotation7_2_1_6 : rotatedStateRow2 sourceState7_1_6 = stateRow7_2_1_6 := by decide
theorem sourceRowRotation7_2_1_7 : rotatedStateRow2 sourceState7_1_7 = stateRow7_2_1_7 := by decide
theorem sourceRowRotation7_2_1_8 : rotatedStateRow2 sourceState7_1_8 = stateRow7_2_1_8 := by decide
theorem sourceRowRotation7_2_1_9 : rotatedStateRow2 sourceState7_1_9 = stateRow7_2_1_9 := by decide
theorem sourceRowRotation7_2_1_10 : rotatedStateRow2 sourceState7_1_10 = stateRow7_2_1_10 := by decide
theorem sourceRowRotation7_2_1_11 : rotatedStateRow2 sourceState7_1_11 = stateRow7_2_1_11 := by decide
theorem initial7_2_1 : (source7_1).map (rotatePatch 2 (hexRegion 5)) = rows0_7_2_1.map Verdict.patch := by
  rw [sourceStates7_1, sourceStateSplit7_1, rotateCanonical_map2]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_2_1_0, sourceRowRotation7_2_1_1, sourceRowRotation7_2_1_2, sourceRowRotation7_2_1_3, sourceRowRotation7_2_1_4, sourceRowRotation7_2_1_5, sourceRowRotation7_2_1_6, sourceRowRotation7_2_1_7, sourceRowRotation7_2_1_8, sourceRowRotation7_2_1_9, sourceRowRotation7_2_1_10, sourceRowRotation7_2_1_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
