module

public import SpectreFinite.RadiusFivePruningBlock7T3C1Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation7_3_1_0 : rotatedStateRow3 sourceState7_1_0 = stateRow7_3_1_0 := by decide
theorem sourceRowRotation7_3_1_1 : rotatedStateRow3 sourceState7_1_1 = stateRow7_3_1_1 := by decide
theorem sourceRowRotation7_3_1_2 : rotatedStateRow3 sourceState7_1_2 = stateRow7_3_1_2 := by decide
theorem sourceRowRotation7_3_1_3 : rotatedStateRow3 sourceState7_1_3 = stateRow7_3_1_3 := by decide
theorem sourceRowRotation7_3_1_4 : rotatedStateRow3 sourceState7_1_4 = stateRow7_3_1_4 := by decide
theorem sourceRowRotation7_3_1_5 : rotatedStateRow3 sourceState7_1_5 = stateRow7_3_1_5 := by decide
theorem sourceRowRotation7_3_1_6 : rotatedStateRow3 sourceState7_1_6 = stateRow7_3_1_6 := by decide
theorem sourceRowRotation7_3_1_7 : rotatedStateRow3 sourceState7_1_7 = stateRow7_3_1_7 := by decide
theorem sourceRowRotation7_3_1_8 : rotatedStateRow3 sourceState7_1_8 = stateRow7_3_1_8 := by decide
theorem sourceRowRotation7_3_1_9 : rotatedStateRow3 sourceState7_1_9 = stateRow7_3_1_9 := by decide
theorem sourceRowRotation7_3_1_10 : rotatedStateRow3 sourceState7_1_10 = stateRow7_3_1_10 := by decide
theorem sourceRowRotation7_3_1_11 : rotatedStateRow3 sourceState7_1_11 = stateRow7_3_1_11 := by decide
theorem initial7_3_1 : (source7_1).map (rotatePatch 3 (hexRegion 5)) = rows0_7_3_1.map Verdict.patch := by
  rw [sourceStates7_1, sourceStateSplit7_1, rotateCanonical_map3]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_3_1_0, sourceRowRotation7_3_1_1, sourceRowRotation7_3_1_2, sourceRowRotation7_3_1_3, sourceRowRotation7_3_1_4, sourceRowRotation7_3_1_5, sourceRowRotation7_3_1_6, sourceRowRotation7_3_1_7, sourceRowRotation7_3_1_8, sourceRowRotation7_3_1_9, sourceRowRotation7_3_1_10, sourceRowRotation7_3_1_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
