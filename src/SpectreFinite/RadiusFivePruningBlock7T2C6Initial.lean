module

public import SpectreFinite.RadiusFivePruningBlock7T2C6Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation7_2_6_0 : rotatedStateRow2 sourceState7_6_0 = stateRow7_2_6_0 := by decide
theorem sourceRowRotation7_2_6_1 : rotatedStateRow2 sourceState7_6_1 = stateRow7_2_6_1 := by decide
theorem sourceRowRotation7_2_6_2 : rotatedStateRow2 sourceState7_6_2 = stateRow7_2_6_2 := by decide
theorem sourceRowRotation7_2_6_3 : rotatedStateRow2 sourceState7_6_3 = stateRow7_2_6_3 := by decide
theorem sourceRowRotation7_2_6_4 : rotatedStateRow2 sourceState7_6_4 = stateRow7_2_6_4 := by decide
theorem sourceRowRotation7_2_6_5 : rotatedStateRow2 sourceState7_6_5 = stateRow7_2_6_5 := by decide
theorem sourceRowRotation7_2_6_6 : rotatedStateRow2 sourceState7_6_6 = stateRow7_2_6_6 := by decide
theorem sourceRowRotation7_2_6_7 : rotatedStateRow2 sourceState7_6_7 = stateRow7_2_6_7 := by decide
theorem sourceRowRotation7_2_6_8 : rotatedStateRow2 sourceState7_6_8 = stateRow7_2_6_8 := by decide
theorem sourceRowRotation7_2_6_9 : rotatedStateRow2 sourceState7_6_9 = stateRow7_2_6_9 := by decide
theorem sourceRowRotation7_2_6_10 : rotatedStateRow2 sourceState7_6_10 = stateRow7_2_6_10 := by decide
theorem sourceRowRotation7_2_6_11 : rotatedStateRow2 sourceState7_6_11 = stateRow7_2_6_11 := by decide
theorem initial7_2_6 : (source7_6).map (rotatePatch 2 (hexRegion 5)) = rows0_7_2_6.map Verdict.patch := by
  rw [sourceStates7_6, sourceStateSplit7_6, rotateCanonical_map2]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_2_6_0, sourceRowRotation7_2_6_1, sourceRowRotation7_2_6_2, sourceRowRotation7_2_6_3, sourceRowRotation7_2_6_4, sourceRowRotation7_2_6_5, sourceRowRotation7_2_6_6, sourceRowRotation7_2_6_7, sourceRowRotation7_2_6_8, sourceRowRotation7_2_6_9, sourceRowRotation7_2_6_10, sourceRowRotation7_2_6_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
