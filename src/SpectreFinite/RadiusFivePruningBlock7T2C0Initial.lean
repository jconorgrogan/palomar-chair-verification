module

public import SpectreFinite.RadiusFivePruningBlock7T2C0Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation7_2_0_0 : rotatedStateRow2 sourceState7_0_0 = stateRow7_2_0_0 := by decide
theorem sourceRowRotation7_2_0_1 : rotatedStateRow2 sourceState7_0_1 = stateRow7_2_0_1 := by decide
theorem sourceRowRotation7_2_0_2 : rotatedStateRow2 sourceState7_0_2 = stateRow7_2_0_2 := by decide
theorem sourceRowRotation7_2_0_3 : rotatedStateRow2 sourceState7_0_3 = stateRow7_2_0_3 := by decide
theorem sourceRowRotation7_2_0_4 : rotatedStateRow2 sourceState7_0_4 = stateRow7_2_0_4 := by decide
theorem sourceRowRotation7_2_0_5 : rotatedStateRow2 sourceState7_0_5 = stateRow7_2_0_5 := by decide
theorem sourceRowRotation7_2_0_6 : rotatedStateRow2 sourceState7_0_6 = stateRow7_2_0_6 := by decide
theorem sourceRowRotation7_2_0_7 : rotatedStateRow2 sourceState7_0_7 = stateRow7_2_0_7 := by decide
theorem sourceRowRotation7_2_0_8 : rotatedStateRow2 sourceState7_0_8 = stateRow7_2_0_8 := by decide
theorem sourceRowRotation7_2_0_9 : rotatedStateRow2 sourceState7_0_9 = stateRow7_2_0_9 := by decide
theorem sourceRowRotation7_2_0_10 : rotatedStateRow2 sourceState7_0_10 = stateRow7_2_0_10 := by decide
theorem sourceRowRotation7_2_0_11 : rotatedStateRow2 sourceState7_0_11 = stateRow7_2_0_11 := by decide
theorem initial7_2_0 : (source7_0).map (rotatePatch 2 (hexRegion 5)) = rows0_7_2_0.map Verdict.patch := by
  rw [sourceStates7_0, sourceStateSplit7_0, rotateCanonical_map2]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_2_0_0, sourceRowRotation7_2_0_1, sourceRowRotation7_2_0_2, sourceRowRotation7_2_0_3, sourceRowRotation7_2_0_4, sourceRowRotation7_2_0_5, sourceRowRotation7_2_0_6, sourceRowRotation7_2_0_7, sourceRowRotation7_2_0_8, sourceRowRotation7_2_0_9, sourceRowRotation7_2_0_10, sourceRowRotation7_2_0_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
