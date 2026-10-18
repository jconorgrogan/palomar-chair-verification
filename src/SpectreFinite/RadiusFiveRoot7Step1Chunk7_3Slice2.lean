module

public import SpectreFinite.RadiusFiveRoot7Part0Segment00
public import SpectreFinite.RadiusFiveRoot7Step1Chunk7_3Rows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root7Node0Step1Chunk7_3_slice2_checked :
    checkNarrowing ⟨table34Scope, RadiusFourPruning.stateRows7_3_2⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)

#print axioms root7Node0Step1Chunk7_3_slice2_checked
end SpectreFinite.HexSearch.RadiusFive
