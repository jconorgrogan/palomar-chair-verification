module

public import SpectreFinite.RadiusFourPruningRoundInitial

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem rows0_count : rows0.length = 1884 := by
  have h := congrArg List.length initial
  simpa only [List.length_map, RadiusFour.allTurnFamily_count] using h
theorem round_counts : [rows0.length, certifiedFamily.length] = [1884, 1836] := by
  rw [rows0_count, certifiedFamily_count]

end SpectreFinite.HexSearch.RadiusFourPruning
