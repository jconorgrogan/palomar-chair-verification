module

public import SpectreFinite.RadiusFivePruningBlock0T3C1Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation0_3_1_0 : rotatedStateRow3 sourceState0_1_0 = stateRow0_3_1_0 := by decide
theorem sourceRowRotation0_3_1_1 : rotatedStateRow3 sourceState0_1_1 = stateRow0_3_1_1 := by decide
theorem sourceRowRotation0_3_1_2 : rotatedStateRow3 sourceState0_1_2 = stateRow0_3_1_2 := by decide
theorem sourceRowRotation0_3_1_3 : rotatedStateRow3 sourceState0_1_3 = stateRow0_3_1_3 := by decide
theorem sourceRowRotation0_3_1_4 : rotatedStateRow3 sourceState0_1_4 = stateRow0_3_1_4 := by decide
theorem sourceRowRotation0_3_1_5 : rotatedStateRow3 sourceState0_1_5 = stateRow0_3_1_5 := by decide
theorem sourceRowRotation0_3_1_6 : rotatedStateRow3 sourceState0_1_6 = stateRow0_3_1_6 := by decide
theorem sourceRowRotation0_3_1_7 : rotatedStateRow3 sourceState0_1_7 = stateRow0_3_1_7 := by decide
theorem sourceRowRotation0_3_1_8 : rotatedStateRow3 sourceState0_1_8 = stateRow0_3_1_8 := by decide
theorem sourceRowRotation0_3_1_9 : rotatedStateRow3 sourceState0_1_9 = stateRow0_3_1_9 := by decide
theorem sourceRowRotation0_3_1_10 : rotatedStateRow3 sourceState0_1_10 = stateRow0_3_1_10 := by decide
theorem sourceRowRotation0_3_1_11 : rotatedStateRow3 sourceState0_1_11 = stateRow0_3_1_11 := by decide
theorem initial0_3_1 : (source0_1).map (rotatePatch 3 (hexRegion 5)) = rows0_0_3_1.map Verdict.patch := by
  rw [sourceStates0_1, sourceStateSplit0_1, rotateCanonical_map3]
  simp only [List.map_cons, List.map_nil, sourceRowRotation0_3_1_0, sourceRowRotation0_3_1_1, sourceRowRotation0_3_1_2, sourceRowRotation0_3_1_3, sourceRowRotation0_3_1_4, sourceRowRotation0_3_1_5, sourceRowRotation0_3_1_6, sourceRowRotation0_3_1_7, sourceRowRotation0_3_1_8, sourceRowRotation0_3_1_9, sourceRowRotation0_3_1_10, sourceRowRotation0_3_1_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
