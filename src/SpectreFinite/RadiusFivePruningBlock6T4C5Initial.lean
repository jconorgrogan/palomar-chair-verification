module

public import SpectreFinite.RadiusFivePruningBlock6T4C5Data
public import SpectreFinite.RadiusFivePruningSourceStates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowRotation6_4_5_0 : rotatedStateRow4 sourceState6_5_0 = stateRow6_4_5_0 := by decide
theorem sourceRowRotation6_4_5_1 : rotatedStateRow4 sourceState6_5_1 = stateRow6_4_5_1 := by decide
theorem sourceRowRotation6_4_5_2 : rotatedStateRow4 sourceState6_5_2 = stateRow6_4_5_2 := by decide
theorem initial6_4_5 : (source6_5).map (rotatePatch 4 (hexRegion 5)) = rows0_6_4_5.map Verdict.patch := by
  rw [sourceStates6_5, sourceStateSplit6_5, rotateCanonical_map4]
  simp only [List.map_cons, List.map_nil, sourceRowRotation6_4_5_0, sourceRowRotation6_4_5_1, sourceRowRotation6_4_5_2] <;> rfl

end SpectreFinite.HexSearch.RadiusFivePruning
