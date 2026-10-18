module

public import SpectreFinite.RadiusFiveRoot8Part0Segment00
public import SpectreFinite.RadiusFiveRoot8Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable33
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root8Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
