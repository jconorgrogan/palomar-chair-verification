module

public import SpectreFinite.RadiusFiveRoot1Part0Segment00
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_2Rows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root1Node0Step1Chunk1_2_slice1_checked :
    checkNarrowing ⟨table34Scope, RadiusFourPruning.stateRows1_2_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)

#print axioms root1Node0Step1Chunk1_2_slice1_checked
end SpectreFinite.HexSearch.RadiusFive
