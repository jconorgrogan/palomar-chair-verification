module

public import SpectreFinite.RadiusFivePruningBlock0T0C2Core
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation0_0_2_0 : rotatedStateRow0 sourceState0_2_0 = stateRow0_0_2_0 := by decide
theorem sourceRowRotation0_0_2_1 : rotatedStateRow0 sourceState0_2_1 = stateRow0_0_2_1 := by decide
theorem sourceRowRotation0_0_2_2 : rotatedStateRow0 sourceState0_2_2 = stateRow0_0_2_2 := by decide
theorem sourceRowRotation0_0_2_3 : rotatedStateRow0 sourceState0_2_3 = stateRow0_0_2_3 := by decide
theorem sourceRowRotation0_0_2_4 : rotatedStateRow0 sourceState0_2_4 = stateRow0_0_2_4 := by decide
theorem sourceRowRotation0_0_2_5 : rotatedStateRow0 sourceState0_2_5 = stateRow0_0_2_5 := by decide
theorem sourceRowRotation0_0_2_6 : rotatedStateRow0 sourceState0_2_6 = stateRow0_0_2_6 := by decide
theorem sourceRowRotation0_0_2_7 : rotatedStateRow0 sourceState0_2_7 = stateRow0_0_2_7 := by decide
theorem sourceRowRotation0_0_2_8 : rotatedStateRow0 sourceState0_2_8 = stateRow0_0_2_8 := by decide
theorem sourceRowRotation0_0_2_9 : rotatedStateRow0 sourceState0_2_9 = stateRow0_0_2_9 := by decide
theorem sourceRowRotation0_0_2_10 : rotatedStateRow0 sourceState0_2_10 = stateRow0_0_2_10 := by decide
theorem sourceRowRotation0_0_2_11 : rotatedStateRow0 sourceState0_2_11 = stateRow0_0_2_11 := by decide
theorem initial0_0_2 : (source0_2).map (rotatePatch 0 (hexRegion 5)) = rows0_0_0_2.map Verdict.patch := by
  rw [sourceStates0_2, sourceStateSplit0_2, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation0_0_2_0, sourceRowRotation0_0_2_1, sourceRowRotation0_0_2_2, sourceRowRotation0_0_2_3, sourceRowRotation0_0_2_4, sourceRowRotation0_0_2_5, sourceRowRotation0_0_2_6, sourceRowRotation0_0_2_7, sourceRowRotation0_0_2_8, sourceRowRotation0_0_2_9, sourceRowRotation0_0_2_10, sourceRowRotation0_0_2_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
