module

public import SpectreFinite.RadiusFourPruningRotationExpansion
public import SpectreFinite.RadiusFourPruningRoundData
public import SpectreFinite.RadiusFourPruningRoundCheck
public import SpectreFinite.RadiusFourPruningRoundInitial
public import SpectreFinite.RadiusFourPruningRoundOutput
public import SpectreFinite.RadiusFourPruningRoundCounts

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem rounds_occurrenceComplete (f : Position → State) (hf : OccurrenceComplete f (hexRegion 4) RadiusFour.allTurnFamily) : OccurrenceComplete f (hexRegion 4) certifiedFamily := by
  have h0 : OccurrenceComplete f (hexRegion 4) (rows0.map Verdict.patch) := by
    rw [initial]
    exact hf
  have h1 := certified_round (hexRegion 4) direction samples0 samples0_shared trees0 rows0 checked0 f h0
  rw [certifiedFamily_eq]
  exact h1
#print axioms rounds_occurrenceComplete

end SpectreFinite.HexSearch.RadiusFourPruning
