module

public import SpectreFinite.RadiusFivePruningBlock5T2C2Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation5_2_2_0 : rotatedStateRow2 sourceState5_2_0 = stateRow5_2_2_0 := by decide
theorem sourceRowRotation5_2_2_1 : rotatedStateRow2 sourceState5_2_1 = stateRow5_2_2_1 := by decide
theorem sourceRowRotation5_2_2_2 : rotatedStateRow2 sourceState5_2_2 = stateRow5_2_2_2 := by decide
theorem sourceRowRotation5_2_2_3 : rotatedStateRow2 sourceState5_2_3 = stateRow5_2_2_3 := by decide
theorem sourceRowRotation5_2_2_4 : rotatedStateRow2 sourceState5_2_4 = stateRow5_2_2_4 := by decide
theorem sourceRowRotation5_2_2_5 : rotatedStateRow2 sourceState5_2_5 = stateRow5_2_2_5 := by decide
theorem sourceRowRotation5_2_2_6 : rotatedStateRow2 sourceState5_2_6 = stateRow5_2_2_6 := by decide
theorem sourceRowRotation5_2_2_7 : rotatedStateRow2 sourceState5_2_7 = stateRow5_2_2_7 := by decide
theorem sourceRowRotation5_2_2_8 : rotatedStateRow2 sourceState5_2_8 = stateRow5_2_2_8 := by decide
theorem sourceRowRotation5_2_2_9 : rotatedStateRow2 sourceState5_2_9 = stateRow5_2_2_9 := by decide
theorem sourceRowRotation5_2_2_10 : rotatedStateRow2 sourceState5_2_10 = stateRow5_2_2_10 := by decide
theorem sourceRowRotation5_2_2_11 : rotatedStateRow2 sourceState5_2_11 = stateRow5_2_2_11 := by decide
theorem initial5_2_2 : (source5_2).map (rotatePatch 2 (hexRegion 5)) = rows0_5_2_2.map Verdict.patch := by
  rw [sourceStates5_2, sourceStateSplit5_2, rotateCanonical_map2]
  simp only [List.map_cons, List.map_nil, sourceRowRotation5_2_2_0, sourceRowRotation5_2_2_1, sourceRowRotation5_2_2_2, sourceRowRotation5_2_2_3, sourceRowRotation5_2_2_4, sourceRowRotation5_2_2_5, sourceRowRotation5_2_2_6, sourceRowRotation5_2_2_7, sourceRowRotation5_2_2_8, sourceRowRotation5_2_2_9, sourceRowRotation5_2_2_10, sourceRowRotation5_2_2_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
