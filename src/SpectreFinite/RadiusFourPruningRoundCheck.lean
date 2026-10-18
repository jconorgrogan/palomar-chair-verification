module

public import SpectreFinite.RadiusFourPruningRoundData

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem checked0 : checkRows direction samples0 trees0 rows0 = true := by
  apply checkRows_flatten
  simp only [chunks0, List.all_cons, List.all_nil, check0_0_0, check0_0_1, check0_0_2, check0_0_3, check0_0_4, check0_0_5, check0_1_0, check0_1_1, check0_1_2, check0_1_3, check0_1_4, check0_1_5, check0_2_0, check0_2_1, check0_2_2, check0_2_3, check0_2_4, check0_2_5, check0_3_0, check0_3_1, check0_3_2, check0_3_3, check0_3_4, check0_3_5, check0_4_0, check0_4_1, check0_4_2, check0_4_3, check0_4_4, check0_4_5, check0_5_0, check0_5_1, check0_5_2, check0_5_3, check0_5_4, check0_5_5, check0_6_0, check0_6_1, check0_6_2, check0_6_3, check0_6_4, check0_6_5, check0_7_0, check0_7_1, check0_7_2, check0_7_3, check0_7_4, check0_7_5, check0_8_0, check0_8_1, check0_8_2, check0_8_3, check0_8_4, check0_8_5, Bool.true_and]

end SpectreFinite.HexSearch.RadiusFourPruning
