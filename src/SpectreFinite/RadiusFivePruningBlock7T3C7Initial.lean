module

public import SpectreFinite.RadiusFivePruningBlock7T3C7Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation7_3_7_0 : rotatedStateRow3 sourceState7_7_0 = stateRow7_3_7_0 := by decide
theorem sourceRowRotation7_3_7_1 : rotatedStateRow3 sourceState7_7_1 = stateRow7_3_7_1 := by decide
theorem sourceRowRotation7_3_7_2 : rotatedStateRow3 sourceState7_7_2 = stateRow7_3_7_2 := by decide
theorem sourceRowRotation7_3_7_3 : rotatedStateRow3 sourceState7_7_3 = stateRow7_3_7_3 := by decide
theorem sourceRowRotation7_3_7_4 : rotatedStateRow3 sourceState7_7_4 = stateRow7_3_7_4 := by decide
theorem sourceRowRotation7_3_7_5 : rotatedStateRow3 sourceState7_7_5 = stateRow7_3_7_5 := by decide
theorem sourceRowRotation7_3_7_6 : rotatedStateRow3 sourceState7_7_6 = stateRow7_3_7_6 := by decide
theorem sourceRowRotation7_3_7_7 : rotatedStateRow3 sourceState7_7_7 = stateRow7_3_7_7 := by decide
theorem sourceRowRotation7_3_7_8 : rotatedStateRow3 sourceState7_7_8 = stateRow7_3_7_8 := by decide
theorem sourceRowRotation7_3_7_9 : rotatedStateRow3 sourceState7_7_9 = stateRow7_3_7_9 := by decide
theorem sourceRowRotation7_3_7_10 : rotatedStateRow3 sourceState7_7_10 = stateRow7_3_7_10 := by decide
theorem sourceRowRotation7_3_7_11 : rotatedStateRow3 sourceState7_7_11 = stateRow7_3_7_11 := by decide
theorem initial7_3_7 : (source7_7).map (rotatePatch 3 (hexRegion 5)) = rows0_7_3_7.map Verdict.patch := by
  rw [sourceStates7_7, sourceStateSplit7_7, rotateCanonical_map3]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_3_7_0, sourceRowRotation7_3_7_1, sourceRowRotation7_3_7_2, sourceRowRotation7_3_7_3, sourceRowRotation7_3_7_4, sourceRowRotation7_3_7_5, sourceRowRotation7_3_7_6, sourceRowRotation7_3_7_7, sourceRowRotation7_3_7_8, sourceRowRotation7_3_7_9, sourceRowRotation7_3_7_10, sourceRowRotation7_3_7_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
