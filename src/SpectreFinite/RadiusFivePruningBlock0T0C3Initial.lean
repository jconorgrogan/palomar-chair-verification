module

public import SpectreFinite.RadiusFivePruningBlock0T0C3Core
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation0_0_3_0 : rotatedStateRow0 sourceState0_3_0 = stateRow0_0_3_0 := by decide
theorem sourceRowRotation0_0_3_1 : rotatedStateRow0 sourceState0_3_1 = stateRow0_0_3_1 := by decide
theorem sourceRowRotation0_0_3_2 : rotatedStateRow0 sourceState0_3_2 = stateRow0_0_3_2 := by decide
theorem sourceRowRotation0_0_3_3 : rotatedStateRow0 sourceState0_3_3 = stateRow0_0_3_3 := by decide
theorem sourceRowRotation0_0_3_4 : rotatedStateRow0 sourceState0_3_4 = stateRow0_0_3_4 := by decide
theorem sourceRowRotation0_0_3_5 : rotatedStateRow0 sourceState0_3_5 = stateRow0_0_3_5 := by decide
theorem sourceRowRotation0_0_3_6 : rotatedStateRow0 sourceState0_3_6 = stateRow0_0_3_6 := by decide
theorem sourceRowRotation0_0_3_7 : rotatedStateRow0 sourceState0_3_7 = stateRow0_0_3_7 := by decide
theorem sourceRowRotation0_0_3_8 : rotatedStateRow0 sourceState0_3_8 = stateRow0_0_3_8 := by decide
theorem sourceRowRotation0_0_3_9 : rotatedStateRow0 sourceState0_3_9 = stateRow0_0_3_9 := by decide
theorem sourceRowRotation0_0_3_10 : rotatedStateRow0 sourceState0_3_10 = stateRow0_0_3_10 := by decide
theorem sourceRowRotation0_0_3_11 : rotatedStateRow0 sourceState0_3_11 = stateRow0_0_3_11 := by decide
theorem initial0_0_3 : (source0_3).map (rotatePatch 0 (hexRegion 5)) = rows0_0_0_3.map Verdict.patch := by
  rw [sourceStates0_3, sourceStateSplit0_3, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation0_0_3_0, sourceRowRotation0_0_3_1, sourceRowRotation0_0_3_2, sourceRowRotation0_0_3_3, sourceRowRotation0_0_3_4, sourceRowRotation0_0_3_5, sourceRowRotation0_0_3_6, sourceRowRotation0_0_3_7, sourceRowRotation0_0_3_8, sourceRowRotation0_0_3_9, sourceRowRotation0_0_3_10, sourceRowRotation0_0_3_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
