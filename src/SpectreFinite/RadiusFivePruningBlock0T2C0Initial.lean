module

public import SpectreFinite.RadiusFivePruningBlock0T2C0Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation0_2_0_0 : rotatedStateRow2 sourceState0_0_0 = stateRow0_2_0_0 := by decide
theorem sourceRowRotation0_2_0_1 : rotatedStateRow2 sourceState0_0_1 = stateRow0_2_0_1 := by decide
theorem sourceRowRotation0_2_0_2 : rotatedStateRow2 sourceState0_0_2 = stateRow0_2_0_2 := by decide
theorem sourceRowRotation0_2_0_3 : rotatedStateRow2 sourceState0_0_3 = stateRow0_2_0_3 := by decide
theorem sourceRowRotation0_2_0_4 : rotatedStateRow2 sourceState0_0_4 = stateRow0_2_0_4 := by decide
theorem sourceRowRotation0_2_0_5 : rotatedStateRow2 sourceState0_0_5 = stateRow0_2_0_5 := by decide
theorem sourceRowRotation0_2_0_6 : rotatedStateRow2 sourceState0_0_6 = stateRow0_2_0_6 := by decide
theorem sourceRowRotation0_2_0_7 : rotatedStateRow2 sourceState0_0_7 = stateRow0_2_0_7 := by decide
theorem sourceRowRotation0_2_0_8 : rotatedStateRow2 sourceState0_0_8 = stateRow0_2_0_8 := by decide
theorem sourceRowRotation0_2_0_9 : rotatedStateRow2 sourceState0_0_9 = stateRow0_2_0_9 := by decide
theorem sourceRowRotation0_2_0_10 : rotatedStateRow2 sourceState0_0_10 = stateRow0_2_0_10 := by decide
theorem sourceRowRotation0_2_0_11 : rotatedStateRow2 sourceState0_0_11 = stateRow0_2_0_11 := by decide
theorem initial0_2_0 : (source0_0).map (rotatePatch 2 (hexRegion 5)) = rows0_0_2_0.map Verdict.patch := by
  rw [sourceStates0_0, sourceStateSplit0_0, rotateCanonical_map2]
  simp only [List.map_cons, List.map_nil, sourceRowRotation0_2_0_0, sourceRowRotation0_2_0_1, sourceRowRotation0_2_0_2, sourceRowRotation0_2_0_3, sourceRowRotation0_2_0_4, sourceRowRotation0_2_0_5, sourceRowRotation0_2_0_6, sourceRowRotation0_2_0_7, sourceRowRotation0_2_0_8, sourceRowRotation0_2_0_9, sourceRowRotation0_2_0_10, sourceRowRotation0_2_0_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
