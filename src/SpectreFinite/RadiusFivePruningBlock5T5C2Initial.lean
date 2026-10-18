module

public import SpectreFinite.RadiusFivePruningBlock5T5C2Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation5_5_2_0 : rotatedStateRow5 sourceState5_2_0 = stateRow5_5_2_0 := by decide
theorem sourceRowRotation5_5_2_1 : rotatedStateRow5 sourceState5_2_1 = stateRow5_5_2_1 := by decide
theorem sourceRowRotation5_5_2_2 : rotatedStateRow5 sourceState5_2_2 = stateRow5_5_2_2 := by decide
theorem sourceRowRotation5_5_2_3 : rotatedStateRow5 sourceState5_2_3 = stateRow5_5_2_3 := by decide
theorem sourceRowRotation5_5_2_4 : rotatedStateRow5 sourceState5_2_4 = stateRow5_5_2_4 := by decide
theorem sourceRowRotation5_5_2_5 : rotatedStateRow5 sourceState5_2_5 = stateRow5_5_2_5 := by decide
theorem sourceRowRotation5_5_2_6 : rotatedStateRow5 sourceState5_2_6 = stateRow5_5_2_6 := by decide
theorem sourceRowRotation5_5_2_7 : rotatedStateRow5 sourceState5_2_7 = stateRow5_5_2_7 := by decide
theorem sourceRowRotation5_5_2_8 : rotatedStateRow5 sourceState5_2_8 = stateRow5_5_2_8 := by decide
theorem sourceRowRotation5_5_2_9 : rotatedStateRow5 sourceState5_2_9 = stateRow5_5_2_9 := by decide
theorem sourceRowRotation5_5_2_10 : rotatedStateRow5 sourceState5_2_10 = stateRow5_5_2_10 := by decide
theorem sourceRowRotation5_5_2_11 : rotatedStateRow5 sourceState5_2_11 = stateRow5_5_2_11 := by decide
theorem initial5_5_2 : (source5_2).map (rotatePatch 5 (hexRegion 5)) = rows0_5_5_2.map Verdict.patch := by
  rw [sourceStates5_2, sourceStateSplit5_2, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation5_5_2_0, sourceRowRotation5_5_2_1, sourceRowRotation5_5_2_2, sourceRowRotation5_5_2_3, sourceRowRotation5_5_2_4, sourceRowRotation5_5_2_5, sourceRowRotation5_5_2_6, sourceRowRotation5_5_2_7, sourceRowRotation5_5_2_8, sourceRowRotation5_5_2_9, sourceRowRotation5_5_2_10, sourceRowRotation5_5_2_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
