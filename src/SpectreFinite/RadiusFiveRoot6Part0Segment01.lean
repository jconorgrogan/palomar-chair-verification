module

public import SpectreFinite.RadiusFiveRoot6Part0Segment00
public import SpectreFinite.RadiusFiveRoot6Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable0
public import SpectreFinite.RadiusFiveTable35
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root6Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
