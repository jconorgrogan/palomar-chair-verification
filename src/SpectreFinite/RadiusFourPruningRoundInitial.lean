module

public import SpectreFinite.RadiusFourPruningRoundData
public import SpectreFinite.RadiusFourPruningRotationExpansion

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem initial : rows0.map Verdict.patch = RadiusFour.allTurnFamily := by
  rw [RadiusFour.allTurnFamily, pruning_rotationClosure_expanded]
  simp only [rows0, List.map_flatten, chunks0, List.map_cons, List.map_nil, ← initial0_0, ← initial0_1, ← initial0_2, ← initial0_3, ← initial0_4, ← initial0_5, ← initial1_0, ← initial1_1, ← initial1_2, ← initial1_3, ← initial1_4, ← initial1_5, ← initial2_0, ← initial2_1, ← initial2_2, ← initial2_3, ← initial2_4, ← initial2_5, ← initial3_0, ← initial3_1, ← initial3_2, ← initial3_3, ← initial3_4, ← initial3_5, ← initial4_0, ← initial4_1, ← initial4_2, ← initial4_3, ← initial4_4, ← initial4_5, ← initial5_0, ← initial5_1, ← initial5_2, ← initial5_3, ← initial5_4, ← initial5_5, ← initial6_0, ← initial6_1, ← initial6_2, ← initial6_3, ← initial6_4, ← initial6_5, ← initial7_0, ← initial7_1, ← initial7_2, ← initial7_3, ← initial7_4, ← initial7_5, ← initial8_0, ← initial8_1, ← initial8_2, ← initial8_3, ← initial8_4, ← initial8_5]
  all_goals rfl

end SpectreFinite.HexSearch.RadiusFourPruning
