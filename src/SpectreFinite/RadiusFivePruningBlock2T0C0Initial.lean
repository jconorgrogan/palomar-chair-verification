module

public import SpectreFinite.RadiusFivePruningBlock2T0C0Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation2_0_0_0 : rotatedStateRow0 sourceState2_0_0 = stateRow2_0_0_0 := by decide
theorem sourceRowRotation2_0_0_1 : rotatedStateRow0 sourceState2_0_1 = stateRow2_0_0_1 := by decide
theorem sourceRowRotation2_0_0_2 : rotatedStateRow0 sourceState2_0_2 = stateRow2_0_0_2 := by decide
theorem sourceRowRotation2_0_0_3 : rotatedStateRow0 sourceState2_0_3 = stateRow2_0_0_3 := by decide
theorem sourceRowRotation2_0_0_4 : rotatedStateRow0 sourceState2_0_4 = stateRow2_0_0_4 := by decide
theorem sourceRowRotation2_0_0_5 : rotatedStateRow0 sourceState2_0_5 = stateRow2_0_0_5 := by decide
theorem initial2_0_0 : (source2_0).map (rotatePatch 0 (hexRegion 5)) = rows0_2_0_0.map Verdict.patch := by
  rw [sourceStates2_0, sourceStateSplit2_0, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation2_0_0_0, sourceRowRotation2_0_0_1, sourceRowRotation2_0_0_2, sourceRowRotation2_0_0_3, sourceRowRotation2_0_0_4, sourceRowRotation2_0_0_5] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
