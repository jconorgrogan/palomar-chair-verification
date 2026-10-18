module

public import SpectreFinite.RadiusFivePruningBlock7T0C2Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation7_0_2_0 : rotatedStateRow0 sourceState7_2_0 = stateRow7_0_2_0 := by decide
theorem sourceRowRotation7_0_2_1 : rotatedStateRow0 sourceState7_2_1 = stateRow7_0_2_1 := by decide
theorem sourceRowRotation7_0_2_2 : rotatedStateRow0 sourceState7_2_2 = stateRow7_0_2_2 := by decide
theorem sourceRowRotation7_0_2_3 : rotatedStateRow0 sourceState7_2_3 = stateRow7_0_2_3 := by decide
theorem sourceRowRotation7_0_2_4 : rotatedStateRow0 sourceState7_2_4 = stateRow7_0_2_4 := by decide
theorem sourceRowRotation7_0_2_5 : rotatedStateRow0 sourceState7_2_5 = stateRow7_0_2_5 := by decide
theorem sourceRowRotation7_0_2_6 : rotatedStateRow0 sourceState7_2_6 = stateRow7_0_2_6 := by decide
theorem sourceRowRotation7_0_2_7 : rotatedStateRow0 sourceState7_2_7 = stateRow7_0_2_7 := by decide
theorem sourceRowRotation7_0_2_8 : rotatedStateRow0 sourceState7_2_8 = stateRow7_0_2_8 := by decide
theorem sourceRowRotation7_0_2_9 : rotatedStateRow0 sourceState7_2_9 = stateRow7_0_2_9 := by decide
theorem sourceRowRotation7_0_2_10 : rotatedStateRow0 sourceState7_2_10 = stateRow7_0_2_10 := by decide
theorem sourceRowRotation7_0_2_11 : rotatedStateRow0 sourceState7_2_11 = stateRow7_0_2_11 := by decide
theorem initial7_0_2 : (source7_2).map (rotatePatch 0 (hexRegion 5)) = rows0_7_0_2.map Verdict.patch := by
  rw [sourceStates7_2, sourceStateSplit7_2, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_0_2_0, sourceRowRotation7_0_2_1, sourceRowRotation7_0_2_2, sourceRowRotation7_0_2_3, sourceRowRotation7_0_2_4, sourceRowRotation7_0_2_5, sourceRowRotation7_0_2_6, sourceRowRotation7_0_2_7, sourceRowRotation7_0_2_8, sourceRowRotation7_0_2_9, sourceRowRotation7_0_2_10, sourceRowRotation7_0_2_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
