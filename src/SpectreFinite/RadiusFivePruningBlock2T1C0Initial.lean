module

public import SpectreFinite.RadiusFivePruningBlock2T1C0Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation2_1_0_0 : rotatedStateRow1 sourceState2_0_0 = stateRow2_1_0_0 := by decide
theorem sourceRowRotation2_1_0_1 : rotatedStateRow1 sourceState2_0_1 = stateRow2_1_0_1 := by decide
theorem sourceRowRotation2_1_0_2 : rotatedStateRow1 sourceState2_0_2 = stateRow2_1_0_2 := by decide
theorem sourceRowRotation2_1_0_3 : rotatedStateRow1 sourceState2_0_3 = stateRow2_1_0_3 := by decide
theorem sourceRowRotation2_1_0_4 : rotatedStateRow1 sourceState2_0_4 = stateRow2_1_0_4 := by decide
theorem sourceRowRotation2_1_0_5 : rotatedStateRow1 sourceState2_0_5 = stateRow2_1_0_5 := by decide
theorem initial2_1_0 : (source2_0).map (rotatePatch 1 (hexRegion 5)) = rows0_2_1_0.map Verdict.patch := by
  rw [sourceStates2_0, sourceStateSplit2_0, rotateCanonical_map1]
  simp only [List.map_cons, List.map_nil, sourceRowRotation2_1_0_0, sourceRowRotation2_1_0_1, sourceRowRotation2_1_0_2, sourceRowRotation2_1_0_3, sourceRowRotation2_1_0_4, sourceRowRotation2_1_0_5] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
