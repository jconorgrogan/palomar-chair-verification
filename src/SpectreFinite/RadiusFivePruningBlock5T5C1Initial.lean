module

public import SpectreFinite.RadiusFivePruningBlock5T5C1Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation5_5_1_0 : rotatedStateRow5 sourceState5_1_0 = stateRow5_5_1_0 := by decide
theorem sourceRowRotation5_5_1_1 : rotatedStateRow5 sourceState5_1_1 = stateRow5_5_1_1 := by decide
theorem sourceRowRotation5_5_1_2 : rotatedStateRow5 sourceState5_1_2 = stateRow5_5_1_2 := by decide
theorem sourceRowRotation5_5_1_3 : rotatedStateRow5 sourceState5_1_3 = stateRow5_5_1_3 := by decide
theorem sourceRowRotation5_5_1_4 : rotatedStateRow5 sourceState5_1_4 = stateRow5_5_1_4 := by decide
theorem sourceRowRotation5_5_1_5 : rotatedStateRow5 sourceState5_1_5 = stateRow5_5_1_5 := by decide
theorem sourceRowRotation5_5_1_6 : rotatedStateRow5 sourceState5_1_6 = stateRow5_5_1_6 := by decide
theorem sourceRowRotation5_5_1_7 : rotatedStateRow5 sourceState5_1_7 = stateRow5_5_1_7 := by decide
theorem sourceRowRotation5_5_1_8 : rotatedStateRow5 sourceState5_1_8 = stateRow5_5_1_8 := by decide
theorem sourceRowRotation5_5_1_9 : rotatedStateRow5 sourceState5_1_9 = stateRow5_5_1_9 := by decide
theorem sourceRowRotation5_5_1_10 : rotatedStateRow5 sourceState5_1_10 = stateRow5_5_1_10 := by decide
theorem sourceRowRotation5_5_1_11 : rotatedStateRow5 sourceState5_1_11 = stateRow5_5_1_11 := by decide
theorem initial5_5_1 : (source5_1).map (rotatePatch 5 (hexRegion 5)) = rows0_5_5_1.map Verdict.patch := by
  rw [sourceStates5_1, sourceStateSplit5_1, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation5_5_1_0, sourceRowRotation5_5_1_1, sourceRowRotation5_5_1_2, sourceRowRotation5_5_1_3, sourceRowRotation5_5_1_4, sourceRowRotation5_5_1_5, sourceRowRotation5_5_1_6, sourceRowRotation5_5_1_7, sourceRowRotation5_5_1_8, sourceRowRotation5_5_1_9, sourceRowRotation5_5_1_10, sourceRowRotation5_5_1_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
