module

public import SpectreFinite.RadiusFivePruningBlock7T5C4Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation7_5_4_0 : rotatedStateRow5 sourceState7_4_0 = stateRow7_5_4_0 := by decide
theorem sourceRowRotation7_5_4_1 : rotatedStateRow5 sourceState7_4_1 = stateRow7_5_4_1 := by decide
theorem sourceRowRotation7_5_4_2 : rotatedStateRow5 sourceState7_4_2 = stateRow7_5_4_2 := by decide
theorem sourceRowRotation7_5_4_3 : rotatedStateRow5 sourceState7_4_3 = stateRow7_5_4_3 := by decide
theorem sourceRowRotation7_5_4_4 : rotatedStateRow5 sourceState7_4_4 = stateRow7_5_4_4 := by decide
theorem sourceRowRotation7_5_4_5 : rotatedStateRow5 sourceState7_4_5 = stateRow7_5_4_5 := by decide
theorem sourceRowRotation7_5_4_6 : rotatedStateRow5 sourceState7_4_6 = stateRow7_5_4_6 := by decide
theorem sourceRowRotation7_5_4_7 : rotatedStateRow5 sourceState7_4_7 = stateRow7_5_4_7 := by decide
theorem sourceRowRotation7_5_4_8 : rotatedStateRow5 sourceState7_4_8 = stateRow7_5_4_8 := by decide
theorem sourceRowRotation7_5_4_9 : rotatedStateRow5 sourceState7_4_9 = stateRow7_5_4_9 := by decide
theorem sourceRowRotation7_5_4_10 : rotatedStateRow5 sourceState7_4_10 = stateRow7_5_4_10 := by decide
theorem sourceRowRotation7_5_4_11 : rotatedStateRow5 sourceState7_4_11 = stateRow7_5_4_11 := by decide
theorem initial7_5_4 : (source7_4).map (rotatePatch 5 (hexRegion 5)) = rows0_7_5_4.map Verdict.patch := by
  rw [sourceStates7_4, sourceStateSplit7_4, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_5_4_0, sourceRowRotation7_5_4_1, sourceRowRotation7_5_4_2, sourceRowRotation7_5_4_3, sourceRowRotation7_5_4_4, sourceRowRotation7_5_4_5, sourceRowRotation7_5_4_6, sourceRowRotation7_5_4_7, sourceRowRotation7_5_4_8, sourceRowRotation7_5_4_9, sourceRowRotation7_5_4_10, sourceRowRotation7_5_4_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
