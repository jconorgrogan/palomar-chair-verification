module

public import SpectreFinite.RadiusFiveRoot5Part0Segment00
public import SpectreFinite.RadiusFiveRoot5Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable25
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root5Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
