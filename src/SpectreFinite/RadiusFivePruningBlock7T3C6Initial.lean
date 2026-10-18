module

public import SpectreFinite.RadiusFivePruningBlock7T3C6Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation7_3_6_0 : rotatedStateRow3 sourceState7_6_0 = stateRow7_3_6_0 := by decide
theorem sourceRowRotation7_3_6_1 : rotatedStateRow3 sourceState7_6_1 = stateRow7_3_6_1 := by decide
theorem sourceRowRotation7_3_6_2 : rotatedStateRow3 sourceState7_6_2 = stateRow7_3_6_2 := by decide
theorem sourceRowRotation7_3_6_3 : rotatedStateRow3 sourceState7_6_3 = stateRow7_3_6_3 := by decide
theorem sourceRowRotation7_3_6_4 : rotatedStateRow3 sourceState7_6_4 = stateRow7_3_6_4 := by decide
theorem sourceRowRotation7_3_6_5 : rotatedStateRow3 sourceState7_6_5 = stateRow7_3_6_5 := by decide
theorem sourceRowRotation7_3_6_6 : rotatedStateRow3 sourceState7_6_6 = stateRow7_3_6_6 := by decide
theorem sourceRowRotation7_3_6_7 : rotatedStateRow3 sourceState7_6_7 = stateRow7_3_6_7 := by decide
theorem sourceRowRotation7_3_6_8 : rotatedStateRow3 sourceState7_6_8 = stateRow7_3_6_8 := by decide
theorem sourceRowRotation7_3_6_9 : rotatedStateRow3 sourceState7_6_9 = stateRow7_3_6_9 := by decide
theorem sourceRowRotation7_3_6_10 : rotatedStateRow3 sourceState7_6_10 = stateRow7_3_6_10 := by decide
theorem sourceRowRotation7_3_6_11 : rotatedStateRow3 sourceState7_6_11 = stateRow7_3_6_11 := by decide
theorem initial7_3_6 : (source7_6).map (rotatePatch 3 (hexRegion 5)) = rows0_7_3_6.map Verdict.patch := by
  rw [sourceStates7_6, sourceStateSplit7_6, rotateCanonical_map3]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_3_6_0, sourceRowRotation7_3_6_1, sourceRowRotation7_3_6_2, sourceRowRotation7_3_6_3, sourceRowRotation7_3_6_4, sourceRowRotation7_3_6_5, sourceRowRotation7_3_6_6, sourceRowRotation7_3_6_7, sourceRowRotation7_3_6_8, sourceRowRotation7_3_6_9, sourceRowRotation7_3_6_10, sourceRowRotation7_3_6_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
