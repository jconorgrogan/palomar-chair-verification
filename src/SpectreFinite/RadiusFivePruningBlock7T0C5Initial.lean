module

public import SpectreFinite.RadiusFivePruningBlock7T0C5Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation7_0_5_0 : rotatedStateRow0 sourceState7_5_0 = stateRow7_0_5_0 := by decide
theorem sourceRowRotation7_0_5_1 : rotatedStateRow0 sourceState7_5_1 = stateRow7_0_5_1 := by decide
theorem sourceRowRotation7_0_5_2 : rotatedStateRow0 sourceState7_5_2 = stateRow7_0_5_2 := by decide
theorem sourceRowRotation7_0_5_3 : rotatedStateRow0 sourceState7_5_3 = stateRow7_0_5_3 := by decide
theorem sourceRowRotation7_0_5_4 : rotatedStateRow0 sourceState7_5_4 = stateRow7_0_5_4 := by decide
theorem sourceRowRotation7_0_5_5 : rotatedStateRow0 sourceState7_5_5 = stateRow7_0_5_5 := by decide
theorem sourceRowRotation7_0_5_6 : rotatedStateRow0 sourceState7_5_6 = stateRow7_0_5_6 := by decide
theorem sourceRowRotation7_0_5_7 : rotatedStateRow0 sourceState7_5_7 = stateRow7_0_5_7 := by decide
theorem sourceRowRotation7_0_5_8 : rotatedStateRow0 sourceState7_5_8 = stateRow7_0_5_8 := by decide
theorem sourceRowRotation7_0_5_9 : rotatedStateRow0 sourceState7_5_9 = stateRow7_0_5_9 := by decide
theorem sourceRowRotation7_0_5_10 : rotatedStateRow0 sourceState7_5_10 = stateRow7_0_5_10 := by decide
theorem sourceRowRotation7_0_5_11 : rotatedStateRow0 sourceState7_5_11 = stateRow7_0_5_11 := by decide
theorem initial7_0_5 : (source7_5).map (rotatePatch 0 (hexRegion 5)) = rows0_7_0_5.map Verdict.patch := by
  rw [sourceStates7_5, sourceStateSplit7_5, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_0_5_0, sourceRowRotation7_0_5_1, sourceRowRotation7_0_5_2, sourceRowRotation7_0_5_3, sourceRowRotation7_0_5_4, sourceRowRotation7_0_5_5, sourceRowRotation7_0_5_6, sourceRowRotation7_0_5_7, sourceRowRotation7_0_5_8, sourceRowRotation7_0_5_9, sourceRowRotation7_0_5_10, sourceRowRotation7_0_5_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
