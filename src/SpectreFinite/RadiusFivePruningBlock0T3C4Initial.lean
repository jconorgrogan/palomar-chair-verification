module

public import SpectreFinite.RadiusFivePruningBlock0T3C4Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation0_3_4_0 : rotatedStateRow3 sourceState0_4_0 = stateRow0_3_4_0 := by decide
theorem sourceRowRotation0_3_4_1 : rotatedStateRow3 sourceState0_4_1 = stateRow0_3_4_1 := by decide
theorem sourceRowRotation0_3_4_2 : rotatedStateRow3 sourceState0_4_2 = stateRow0_3_4_2 := by decide
theorem sourceRowRotation0_3_4_3 : rotatedStateRow3 sourceState0_4_3 = stateRow0_3_4_3 := by decide
theorem sourceRowRotation0_3_4_4 : rotatedStateRow3 sourceState0_4_4 = stateRow0_3_4_4 := by decide
theorem sourceRowRotation0_3_4_5 : rotatedStateRow3 sourceState0_4_5 = stateRow0_3_4_5 := by decide
theorem sourceRowRotation0_3_4_6 : rotatedStateRow3 sourceState0_4_6 = stateRow0_3_4_6 := by decide
theorem sourceRowRotation0_3_4_7 : rotatedStateRow3 sourceState0_4_7 = stateRow0_3_4_7 := by decide
theorem sourceRowRotation0_3_4_8 : rotatedStateRow3 sourceState0_4_8 = stateRow0_3_4_8 := by decide
theorem sourceRowRotation0_3_4_9 : rotatedStateRow3 sourceState0_4_9 = stateRow0_3_4_9 := by decide
theorem sourceRowRotation0_3_4_10 : rotatedStateRow3 sourceState0_4_10 = stateRow0_3_4_10 := by decide
theorem sourceRowRotation0_3_4_11 : rotatedStateRow3 sourceState0_4_11 = stateRow0_3_4_11 := by decide
theorem initial0_3_4 : (source0_4).map (rotatePatch 3 (hexRegion 5)) = rows0_0_3_4.map Verdict.patch := by
  rw [sourceStates0_4, sourceStateSplit0_4, rotateCanonical_map3]
  simp only [List.map_cons, List.map_nil, sourceRowRotation0_3_4_0, sourceRowRotation0_3_4_1, sourceRowRotation0_3_4_2, sourceRowRotation0_3_4_3, sourceRowRotation0_3_4_4, sourceRowRotation0_3_4_5, sourceRowRotation0_3_4_6, sourceRowRotation0_3_4_7, sourceRowRotation0_3_4_8, sourceRowRotation0_3_4_9, sourceRowRotation0_3_4_10, sourceRowRotation0_3_4_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
