module

public import SpectreFinite.RadiusFiveRoot5Part0Segment00
public import SpectreFinite.RadiusFiveRoot5Step1Chunk5_0Rows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root5Node0Step1Chunk5_0_slice0_checked :
    checkNarrowing ⟨table56Scope, RadiusFourPruning.stateRows5_0_0⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)

#print axioms root5Node0Step1Chunk5_0_slice0_checked
end SpectreFinite.HexSearch.RadiusFive
