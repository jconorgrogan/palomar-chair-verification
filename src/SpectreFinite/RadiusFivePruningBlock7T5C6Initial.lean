module

public import SpectreFinite.RadiusFivePruningBlock7T5C6Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation7_5_6_0 : rotatedStateRow5 sourceState7_6_0 = stateRow7_5_6_0 := by decide
theorem sourceRowRotation7_5_6_1 : rotatedStateRow5 sourceState7_6_1 = stateRow7_5_6_1 := by decide
theorem sourceRowRotation7_5_6_2 : rotatedStateRow5 sourceState7_6_2 = stateRow7_5_6_2 := by decide
theorem sourceRowRotation7_5_6_3 : rotatedStateRow5 sourceState7_6_3 = stateRow7_5_6_3 := by decide
theorem sourceRowRotation7_5_6_4 : rotatedStateRow5 sourceState7_6_4 = stateRow7_5_6_4 := by decide
theorem sourceRowRotation7_5_6_5 : rotatedStateRow5 sourceState7_6_5 = stateRow7_5_6_5 := by decide
theorem sourceRowRotation7_5_6_6 : rotatedStateRow5 sourceState7_6_6 = stateRow7_5_6_6 := by decide
theorem sourceRowRotation7_5_6_7 : rotatedStateRow5 sourceState7_6_7 = stateRow7_5_6_7 := by decide
theorem sourceRowRotation7_5_6_8 : rotatedStateRow5 sourceState7_6_8 = stateRow7_5_6_8 := by decide
theorem sourceRowRotation7_5_6_9 : rotatedStateRow5 sourceState7_6_9 = stateRow7_5_6_9 := by decide
theorem sourceRowRotation7_5_6_10 : rotatedStateRow5 sourceState7_6_10 = stateRow7_5_6_10 := by decide
theorem sourceRowRotation7_5_6_11 : rotatedStateRow5 sourceState7_6_11 = stateRow7_5_6_11 := by decide
theorem initial7_5_6 : (source7_6).map (rotatePatch 5 (hexRegion 5)) = rows0_7_5_6.map Verdict.patch := by
  rw [sourceStates7_6, sourceStateSplit7_6, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_5_6_0, sourceRowRotation7_5_6_1, sourceRowRotation7_5_6_2, sourceRowRotation7_5_6_3, sourceRowRotation7_5_6_4, sourceRowRotation7_5_6_5, sourceRowRotation7_5_6_6, sourceRowRotation7_5_6_7, sourceRowRotation7_5_6_8, sourceRowRotation7_5_6_9, sourceRowRotation7_5_6_10, sourceRowRotation7_5_6_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
