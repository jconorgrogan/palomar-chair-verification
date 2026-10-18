module

public import SpectreFinite.RadiusFiveRoot4Part0Segment00
public import SpectreFinite.RadiusFiveRoot4Step1Chunk4_3Rows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root4Node0Step1Chunk4_3_slice1_checked :
    checkNarrowing ⟨table56Scope, RadiusFourPruning.stateRows4_3_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)

#print axioms root4Node0Step1Chunk4_3_slice1_checked
end SpectreFinite.HexSearch.RadiusFive
