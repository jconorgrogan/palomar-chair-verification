module

public import SpectreFinite.RadiusFivePruningBlock3T5C0Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation3_5_0_0 : rotatedStateRow5 sourceState3_0_0 = stateRow3_5_0_0 := by decide
theorem sourceRowRotation3_5_0_1 : rotatedStateRow5 sourceState3_0_1 = stateRow3_5_0_1 := by decide
theorem sourceRowRotation3_5_0_2 : rotatedStateRow5 sourceState3_0_2 = stateRow3_5_0_2 := by decide
theorem sourceRowRotation3_5_0_3 : rotatedStateRow5 sourceState3_0_3 = stateRow3_5_0_3 := by decide
theorem sourceRowRotation3_5_0_4 : rotatedStateRow5 sourceState3_0_4 = stateRow3_5_0_4 := by decide
theorem sourceRowRotation3_5_0_5 : rotatedStateRow5 sourceState3_0_5 = stateRow3_5_0_5 := by decide
theorem sourceRowRotation3_5_0_6 : rotatedStateRow5 sourceState3_0_6 = stateRow3_5_0_6 := by decide
theorem initial3_5_0 : (source3_0).map (rotatePatch 5 (hexRegion 5)) = rows0_3_5_0.map Verdict.patch := by
  rw [sourceStates3_0, sourceStateSplit3_0, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation3_5_0_0, sourceRowRotation3_5_0_1, sourceRowRotation3_5_0_2, sourceRowRotation3_5_0_3, sourceRowRotation3_5_0_4, sourceRowRotation3_5_0_5, sourceRowRotation3_5_0_6] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
