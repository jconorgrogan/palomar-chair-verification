module

public import SpectreFinite.RadiusFourRoot8Part0Segment00
public import SpectreFinite.RadiusFourRoot8Step1Chunk8_3Rows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root8Node0Step1Chunk8_3_slice0_checked :
    checkNarrowing ⟨table30Scope, RadiusThreePruning.stateRows8_3_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)

#print axioms root8Node0Step1Chunk8_3_slice0_checked
end SpectreFinite.HexSearch.RadiusFour
