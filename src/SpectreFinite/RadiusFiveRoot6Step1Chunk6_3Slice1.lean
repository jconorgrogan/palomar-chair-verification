module

public import SpectreFinite.RadiusFiveRoot6Part0Segment00
public import SpectreFinite.RadiusFiveRoot6Step1Chunk6_3Rows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root6Node0Step1Chunk6_3_slice1_checked :
    checkNarrowing ⟨table35Scope, RadiusFourPruning.stateRows6_3_1⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)

#print axioms root6Node0Step1Chunk6_3_slice1_checked
end SpectreFinite.HexSearch.RadiusFive
