module

public import SpectreFinite.RadiusFiveRoot1Part0Segment00
public import SpectreFinite.RadiusFiveRoot1Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable2
public import SpectreFinite.RadiusFiveTable34
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root1Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
