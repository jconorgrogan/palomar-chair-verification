module

public import SpectreFinite.RadiusFiveRoot7Part0Segment00
public import SpectreFinite.RadiusFiveRoot7Data
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
theorem root7Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_0⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
